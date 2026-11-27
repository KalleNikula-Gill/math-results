"""Export the live C++ DAG, a state map, and a binary case certificate.

The Lean checks can treat these as untrusted data. Each emitted split refers
to one incompatible record pair. The C++ compulsory-tag calculation is only
a heuristic for choosing which split to emit.
"""
from pathlib import Path
import hashlib
import subprocess
import tempfile

project = Path(__file__).resolve().parents[1]
source = (project / 'verify_k28.cpp').read_text()
assert hashlib.sha256(source.encode()).hexdigest() == '6122f11b96d14ff687508a30e0c558ea05274c987d69da3d65d3030bf39c9975'
source = '#include <fstream>\n#include <string>\n' + source
source = source.replace('        memo.clear();', r'''
        // IDs are biased by one: zero is dead; one accepts.
        std::vector<int> alias(nodes.size());
        std::vector<std::vector<int>> unique(1);
        std::map<std::vector<int>, int> dictionary;
        for (int id = 1; id <= root; ++id) {
            std::vector<int> arcs;
            for (auto e : nodes[id]) arcs.push_back(alias[e.child]*128 + e.tag + 1);
            std::sort(arcs.begin(),arcs.end());
            arcs.erase(std::unique(arcs.begin(),arcs.end()),arcs.end());
            if (arcs.size()==1 && arcs[0]%128==0) {
                alias[id]=arcs[0]/128;
            } else {
                auto [it, inserted]=dictionary.emplace(arcs, int(unique.size()));
                if (inserted) unique.push_back(arcs);
                alias[id]=it->second;
            }
        }
        const std::string dir = "SweepCore/Certificates/";
        std::ofstream out(dir + "graph"+std::to_string(m)+".txt");
        for (auto& arcs : unique) {
            for (int i=0; i<int(arcs.size()); ++i) out << (i ? " " : "") << arcs[i];
            out << '\n';
        }
        std::ofstream states(dir + "states"+std::to_string(m)+".txt");
        states << reversed << " 1\n";
        int live=1;
        for (size_t si=0; si<shapes.size(); ++si) {
            const Counts& c=shapes[si].count;
            unsigned code=c[0]*256;
            for (int j=1;j<gates;++j) code+=(c[j]-c[j-1])<<(j-1);
            for (auto kv: memo[si]) if(kv.second>=0){
                states << ((Order(code)<<40)|kv.first) << ' ' << (1+alias[kv.second]) << '\n';
                ++live;
            }
        }
        std::cerr<<"size "<<m<<" live "<<live<<" compact "<<unique.size()
                 <<" compact root "<<alias[root]<<"\n";
        memo.clear();''')
source = source[:source.index('int main() {')] + r'''
std::string subtree(const std::array<const Group*,3>& group,
                    const std::vector<Conflict>& conflicts,
                    const std::array<Tags,3>& bans) {
    std::array<Answer,3> a;
    for (int i=0; i<3; ++i) {
        a[i]=group[i]->evaluate(bans[i],true);
        if (a[i].score<0) return ".leaf";
    }
    int total=a[0].score+a[1].score+a[2].score;
    if (total<50) return ".leaf";
    if (total!=50) throw std::logic_error("uncertified score");
    int chosen=-1;
    for (int k=0;k<int(conflicts.size());k++) {
        auto c=conflicts[k];int tx=tag(c.gx,c.rx),ty=tag(c.gy,c.ry);
        if(bans[c.x].test(tx)||bans[c.y].test(ty))continue;
        bool x=a[c.x].required.test(tx), y=a[c.y].required.test(ty);
        if(x&&y){chosen=k;break;}
        if(chosen<0&&(x||y))chosen=k;
    }
    if(chosen<0)throw std::logic_error("no split");
    auto c=conflicts[chosen]; auto left=bans, right=bans;
    left[c.x].set(tag(c.gx,c.rx));right[c.y].set(tag(c.gy,c.ry));
    return "(.split "+std::to_string(chosen)+" "+subtree(group,conflicts,left)
           +" "+subtree(group,conflicts,right)+")";
}
int main(){
    Group ten(10), nine(9);
    std::array<const Group*,3> group{&ten,&nine,&nine};
    auto values10=ten.central_table(), values9=nine.central_table();
    auto cs=make_conflicts({10,9,9});
    std::vector<Conflict> ctr;
    for(auto c:cs)if(c.gx==14)ctr.push_back(c);
    for(int owner=0;owner<2048;++owner){
        std::array<int,3> allowed{511,255,255};
        for(int j=0;j<int(ctr.size());++j){
            auto c=ctr[j];
            if(owner&(1<<j))allowed[c.y]&=~(1<<(c.ry-1));
            else allowed[c.x]&=~(1<<(c.rx-1));
        }
        int a=values10[allowed[0]], b=values9[allowed[1]], c=values9[allowed[2]];
        if(a<0||b<0||c<0||a+b+c<50)continue;
        std::array<Tags,3> bans;
        for(int i=0;i<3;++i)bans[i]=group[i]->central_bans(allowed[i]);
        std::cout<<"  | "<<owner<<" => "<<subtree(group,cs,bans)<<"\n";
    }
}
'''
(project / 'SweepCore/Certificates').mkdir(exist_ok=True)
with tempfile.TemporaryDirectory() as tmp:
    src = Path(tmp) / 'export.cpp'
    src.write_text(source)
    exe = Path(tmp) / 'export'
    subprocess.run(['c++', '-std=c++17', '-O3', str(src), '-o', str(exe)], check=True)
    result = subprocess.run([str(exe)], cwd=project, stdout=subprocess.PIPE, text=True, check=True)
(project / 'SweepCore/CaseTree.lean').write_text('''namespace K28.Finite

inductive CaseTree where
  | leaf
  | split (conflict : Nat) (left right : CaseTree)
deriving Inhabited

def extraCases : Nat → CaseTree
'''+result.stdout+'''  | _ => .leaf

end K28.Finite
''')
