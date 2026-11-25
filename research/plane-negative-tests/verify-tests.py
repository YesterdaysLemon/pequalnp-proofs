"""Verify negative test families, geometry, and the tight counting cases."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import json
import runpy

root = Path(__file__).resolve().parent
geometry = runpy.run_path(str(root / "plane-dual.py"))


def verify(q, tests, weight, capacity, forbidden_divisor):
    edges, points, lines, popcount, _, _ = geometry["points_lines"](q)
    n = q*q + q + 1
    incidence = set(edges)
    assert all(sum(x == p for x, _ in edges) == q+1 for p in range(n))
    assert all(sum((a,l) in incidence and (b,l) in incidence for l in range(n)) == 1
               for a,b in combinations(range(n), 2))
    maximal = [int(p) | (int(l) << n) for p,l in zip(points,lines)]
    samples = [sum(1 << v for v in s) for s in tests]
    assert all(any(s & ~m == 0 for m in maximal) for s in samples)
    pairs = [(a,b) for a,b in combinations(range(2*n), 2)
             if not (a<n<=b and (a,b-n) in incidence)]
    assert all(any(s >> a & s >> b & 1 for s in samples) for a,b in pairs)
    pp = n*(n-1)//2
    mixed = n*n-len(edges)
    total = 2*pp + weight*mixed
    assert total % capacity == 0
    required = pp if q == 2 else mixed
    assert required % forbidden_divisor != 0
    shapes = Counter(zip(map(int,popcount[points]),map(int,popcount[lines])))
    for p,l in shapes:
        assert (p+q)*(l+q) <= q*(q+1)**2
        a,b=p*(p-1)//2,l*(l-1)//2
        size=a+b+weight*p*l
        assert size <= capacity
        if size == capacity:
            component = a if q == 2 else p*l
            assert component % forbidden_divisor == 0
    print(f"Plane of order {q}: {len(pairs)} pairs, {len(tests)} explicit tests, lower bound {total//capacity+1}.")


if __name__ == "__main__":
    n=7
    edges=set(geometry["points_lines"](2)[0])
    fano=[[p]+[n+l for l in range(n) if (p,l) not in edges] for p in range(n)] + [list(range(n))]
    verify(2,fano,4,22,6)
    verify(4,json.loads((root/"small-suite.json").read_bytes()),5,210,36)
