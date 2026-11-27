// Exact finite calculation for the 28-point crossing problem.
// Build with: c++ -O3 -std=c++17 verify_k28.cpp -o verify_k28
// Run with: ./verify_k28
// The program uses integer arithmetic and the C++ standard library.

#include <algorithm>
#include <array>
#include <bitset>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <map>
#include <numeric>
#include <stdexcept>
#include <unordered_map>
#include <utility>
#include <vector>

namespace {
constexpr int n = 28, first_gate = 10, last_gate = 18, middle = 14;
constexpr int gates = last_gate - first_gate + 1, stride = 10;
constexpr int tag_count = gates * stride;
using Tags = std::bitset<tag_count>;
using Counts = std::array<int, gates>;
using Order = std::uint64_t;  // One four-bit label per position, starting at position 0.

int tag(int gate, int rank) { return (gate - first_gate) * stride + rank - 1; }
int label_at(Order order, int position) { return (order >> (4 * position)) & 15; }
bool is_halving(int t) { return t >= 0 && first_gate + t / stride == middle; }

struct Edge { int child, tag; };
struct LocalMove { int gate, rank; };
struct Shape {
    Counts count{};
    std::array<int, gates> drop{};  // Destination after one external swap, or -1.
    std::vector<LocalMove> internal;
};
struct Answer {
    int score = -1;                 // -1 means no path to the accepting state.
    Tags required;                  // Tags on every path attaining score.
};

class Group {
    int m;
    int radius[stride][stride]{};
    std::array<int, gates> protected_prefix{};
    std::vector<Shape> shapes;
    std::vector<std::unordered_map<Order, int>> memo;
    std::vector<std::vector<Edge>> nodes{{}};  // Node 0 is the accepting state.
    Order reversed = 0;
    int root = -1;

    void make_bounds() {
        for (auto& row : radius) std::fill(row, row + stride, 4);
        for (int d = 4; d >= 1; --d) {
            const int width = 2 * d + 1;
            // All optimal cuts of the ordered labels into a prefix and suffix.
            const int first_cut = (m - width) / 2;
            const int last_cut = (m - width + 1) / 2;
            for (int cut = first_cut; cut <= last_cut; ++cut) {
                for (int a = 0; a < m; ++a)
                    for (int b = 0; b < m; ++b)
                        if ((a < cut) == (b < cut)) radius[a][b] = d;
            }
            for (int g = middle - d; g <= middle + d; ++g)
                protected_prefix[g - first_gate] = last_cut;
        }
    }

    std::map<Counts, int> make_shapes() {
        std::map<Counts, int> index;
        for (int left = 0; left <= m; ++left) {
            for (int mask = 0; mask < (1 << (gates - 1)); ++mask) {
                Shape s;
                s.count[0] = left;
                for (int j = 1; j < gates; ++j)
                    s.count[j] = s.count[j-1] + ((mask >> (j-1)) & 1);
                if (s.count.back() > m) continue;
                s.drop.fill(-1);
                index.emplace(s.count, int(shapes.size()));
                shapes.push_back(s);
            }
        }
        for (Shape& s : shapes) {
            for (int j = 0; j < gates; ++j) {
                int r = s.count[j];
                if (r == 0) continue;
                if (j > 0 && s.count[j-1] == r) continue;
                // The group occupies the left position at this gate, or it
                // can do so at the unobserved boundary of the tracked region.
                if (j == gates - 1 || s.count[j+1] == r) {
                    Counts next = s.count;
                    --next[j];
                    s.drop[j] = index.at(next);
                }
                if (r < m && (j == gates - 1 || s.count[j+1] > r))
                    s.internal.push_back({first_gate + j, r});
            }
        }
        return index;
    }

    int build(int shape, Order order) {
        auto& cache = memo[shape];
        auto found = cache.find(order);
        if (found != cache.end()) return found->second;
        const Shape& s = shapes[shape];
        if (s.count.back() == 0 && order == reversed) return 0;

        std::vector<Edge> edges;
        for (auto [g, r] : s.internal) {
            int a = label_at(order, r-1), b = label_at(order, r);
            if (a >= b || std::abs(g - middle) > radius[a][b]) continue;
            Order bits = Order(a ^ b);
            Order next = order ^ (bits << (4 * (r-1))) ^ (bits << (4 * r));
            int child = build(shape, next);
            if (child >= 0) edges.push_back({child, tag(g, r)});
        }
        for (int j = 0; j < gates; ++j) {
            if (s.drop[j] < 0) continue;
            int a = label_at(order, s.count[j] - 1);
            if (a < protected_prefix[j]) continue;
            int child = build(s.drop[j], order);
            if (child >= 0) edges.push_back({child, -1});
        }
        int id = -1;
        if (!edges.empty()) {
            id = int(nodes.size());
            nodes.push_back(std::move(edges));
        }
        cache.emplace(order, id);
        return id;
    }

public:
    explicit Group(int size) : m(size) {
        make_bounds();
        auto index = make_shapes();
        Counts start;
        start.fill(m);
        Order identity = 0;
        for (int i = 0; i < m; ++i) {
            identity |= Order(i) << (4 * i);
            reversed |= Order(m-1-i) << (4 * i);
        }
        memo.resize(shapes.size());
        root = build(index.at(start), identity);
        if (root < 0) throw std::logic_error("No accepting path");
        memo.clear();
    }

    Tags central_bans(int allowed) const {
        Tags bans;
        for (int r = 1; r < m; ++r)
            if (!(allowed & (1 << (r-1)))) bans.set(tag(middle, r));
        return bans;
    }

    // Children always precede their parents. On ties, intersect the sets of
    // compulsory tags. Turning off this calculation leaves just longest path.
    Answer evaluate(const Tags& bans, bool need_required) const {
        std::vector<int> score(nodes.size(), -1);
        std::vector<Tags> required(need_required ? nodes.size() : 0);
        score[0] = 0;
        for (int v = 1; v <= root; ++v) {
            for (auto [child, t] : nodes[v]) {
                if (score[child] < 0 || (t >= 0 && bans.test(t))) continue;
                int value = score[child] + int(is_halving(t));
                if (value < score[v]) continue;
                if (need_required) {
                    Tags path = required[child];
                    if (t >= 0) path.set(t);
                    if (value > score[v]) required[v] = path;
                    else required[v] &= path;
                }
                score[v] = value;
            }
        }
        return {score[root], need_required ? required[root] : Tags{}};
    }

    std::vector<int> central_table() const {
        std::vector<int> values(1 << (m-1));
        for (int mask = 0; mask < int(values.size()); ++mask)
            values[mask] = evaluate(central_bans(mask), false).score;
        return values;
    }
};

struct Conflict { int x, y, gx, rx, gy, ry; };

std::vector<Conflict> make_conflicts(const std::array<int, 3>& sizes) {
    std::vector<Conflict> result;
    for (int x = 0; x < 3; ++x) {
        int y = (x+1) % 3;
        for (int g = first_gate; g <= last_gate; ++g) {
            for (int d = 1; d < sizes[x] + sizes[y] - g; ++d)
                result.push_back({x, y, g, g - sizes[y] + d, n-g, d});
        }
    }
    return result;
}
} // namespace

int main() {
    const std::array<int, 3> sizes{10, 9, 9};
    const Group ten(10), nine(9);
    const std::array<const Group*, 3> group{&ten, &nine, &nine};
    const auto values10 = ten.central_table(), values9 = nine.central_table();
    const auto conflicts = make_conflicts(sizes);
    std::vector<Conflict> central;
    for (auto c : conflicts) if (c.gx == middle) central.push_back(c);

    const int assignments = 1 << central.size();
    int below = 0, direct = 0, propagated = 0, survivors = 0;
    int largest_bound = -1;
    for (int owner = 0; owner < assignments; ++owner) {
        std::array<int, 3> allowed{511, 255, 255};
        for (int k = 0; k < int(central.size()); ++k) {
            auto c = central[k];
            if (owner & (1 << k)) allowed[c.y] &= ~(1 << (c.ry-1));
            else allowed[c.x] &= ~(1 << (c.rx-1));
        }
        std::array<int, 3> h{values10[allowed[0]], values9[allowed[1]], values9[allowed[2]]};
        if (*std::min_element(h.begin(), h.end()) < 0) { ++below; continue; }
        int sum = std::accumulate(h.begin(), h.end(), 0);
        largest_bound = std::max(largest_bound, sum);
        if (sum < 50) { ++below; continue; }
        if (sum > 50) { ++survivors; continue; }

        std::array<Tags, 3> bans;
        for (int i = 0; i < 3; ++i) bans[i] = group[i]->central_bans(allowed[i]);
        for (int round = 0; ; ++round) {
            std::array<Answer, 3> a;
            bool lost = false;
            for (int i = 0; i < 3; ++i) {
                a[i] = group[i]->evaluate(bans[i], true);
                if (a[i].score < h[i]) lost = true;
            }
            if (lost) { ++propagated; break; }
            auto next = bans;
            bool clash = false;
            for (auto c : conflicts) {
                int tx = tag(c.gx, c.rx), ty = tag(c.gy, c.ry);
                bool x = a[c.x].required.test(tx), y = a[c.y].required.test(ty);
                if (x && y) { clash = true; break; }
                if (x) next[c.y].set(ty);
                if (y) next[c.x].set(tx);
            }
            if (clash) {
                if (round == 0) ++direct; else ++propagated;
                break;
            }
            if (next == bans) { ++survivors; break; }
            bans = next;
        }
    }
    std::cout << "Central assignments: " << assignments
              << "\nLargest initial sum: " << largest_bound
              << "\nInfeasible or below 50: " << below
              << "\nImmediate compulsory conflicts: " << direct
              << "\nExcluded after propagation: " << propagated
              << "\nSurvivors: " << survivors << '\n';
    return survivors == 0 ? 0 : 1;
}
