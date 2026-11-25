from itertools import combinations
from pathlib import Path
import json
import runpy

root = Path(__file__).resolve().parent
plane = runpy.run_path(str(root / "plane-dual.py"))
edges, points, lines, pop, _, _ = plane["points_lines"](3)
incidence = set(edges)
nonincident = [set(j for j in range(13) if (i,j) not in incidence) for i in range(13)]
assert all(len(a & b) == (9 if i == j else 6)
           for i,a in enumerate(nonincident) for j,b in enumerate(nonincident))
shapes = {(int(p),int(l)) for p,l in zip(pop[points],pop[lines])}
assert max(p*l for p,l in shapes) == 12
assert {(p,l) for p,l in shapes if p*l == 12} == {(2,6),(6,2),(3,4),(4,3)}
tests = json.loads((root/"order-three-suite.json").read_bytes())
assert all(len(t) == len(set(t)) and all(0 <= v < 26 for v in t) for t in tests)
assert all(all(not (p in t and l+13 in t) for p,l in edges) for t in tests)
pairs = [(i,j) for i,j in combinations(range(26),2) if not(i<13<=j and (i,j-13) in incidence)]
assert len(pairs) == 273 and all(any(i in t and j in t for t in tests) for i,j in pairs)
print("Verified 273 nonadjacent pairs, 117 nonincidences, and", len(tests), "negative tests.")
