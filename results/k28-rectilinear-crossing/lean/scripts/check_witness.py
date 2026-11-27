"""Check the displayed integer drawing independently of the Lean evaluator."""
from itertools import combinations
from pathlib import Path
import re

root = Path(__file__).resolve().parents[1]
source = (root / "K28/Coordinates.lean").read_text()
block = source.split(":= #[", 1)[1].split("]", 1)[0]
pattern = r"\((-?\d+),\s*(-?\d+)\)"
points = [tuple(map(int, row)) for row in re.findall(pattern, block)]
assert len(points) == len(set(points)) == 28
assert re.fullmatch(r"[\s,]*", re.sub(pattern, "", block))


def orient(a, b, c):
    return (b[0]-a[0])*(c[1]-a[1]) - (b[1]-a[1])*(c[0]-a[0])


def cross(a, b, c, d):
    return (orient(a,b,c)*orient(a,b,d) < 0
            and orient(c,d,a)*orient(c,d,b) < 0)


triples = [abs(orient(*triple)) for triple in combinations(points, 3)]
assert len(triples) == 3276 and min(triples) == 286336
profile = [0]*14
for a, b in combinations(points, 2):
    left = sum(orient(a,b,c) > 0 for c in points)
    right = sum(orient(a,b,c) < 0 for c in points)
    assert left + right == 26
    profile[min(left, right)] += 1

crossings = 0
quartets = 0
for a, b, c, d in combinations(points, 4):
    crossings += cross(a,b,c,d) + cross(a,c,b,d) + cross(a,d,b,c)
    quartets += 1

assert quartets == 20475
assert crossings == 7234
assert crossings == 3*quartets - sum(k*(26-k)*e for k, e in enumerate(profile))
assert profile == [3,6,9,12,15,18,21,24,27,32,38,44,66,63]
print(f"{len(points)} distinct points, {len(triples)} nondegenerate triples")
print(f"Least absolute signed double area: {min(triples)}")
print(f"{quartets} quartets, {crossings} unordered crossing pairs")
print("Edge profile:", *profile)
