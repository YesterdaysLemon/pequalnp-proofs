"""A cycle restriction and an elimination order for the 26-input promise."""
from itertools import combinations

from generic_patch import LINE, N, generic


def neighbors(a,b):
    p,l = sorted((a,b))
    return p < N <= l and bool(LINE[l-N] & (1 << p))


def certificate():
    points = next(quad for quad in combinations(range(N),4)
                  if all(sum((line >> p) & 1 for p in quad) <= 2 for line in LINE))
    order = []
    for a,b in zip(points,points[1:]+points[:1]):
        line, = [l+N for l in range(N) if neighbors(a,l+N) and neighbors(b,l+N)]
        order.extend((a,line))
    assert all(neighbors(i,j) == ((u-v) % 8 in (1,7)) for u,i in enumerate(order)
               for v,j in enumerate(order))
    parents = []
    while len(order) != 2*N:
        child, parent = next((v,j) for v in range(2*N) if v not in order
                             for j,u in enumerate(order) if neighbors(v,u))
        parents.append(parent)
        order.append(child)
    all_neg = [p | (l << N) for p,l in generic()]
    def embed(m):
        return sum(1 << order[i] for i in range(8) if m >> i & 1)
    maximal = []
    def cycle(m):
        return any((m >> i & 1) and (m >> ((i+1)%8) & 1) for i in range(8))
    for m in range(256):
        if not cycle(m) and all(cycle(m | (1 << i)) for i in range(8) if not m >> i & 1):
            maximal.append(m)
    required = [embed(m) for m in maximal] + [1 << v for v in range(2*N)]
    witnesses = []
    while required:
        best = max(all_neg,key=lambda row: sum(m & row == m for m in required))
        assert any(m & best == m for m in required)
        witnesses.append(best)
        required = [m for m in required if m & best != m]
    assert all(any(m & v == m for v in witnesses) for m in map(embed,maximal))
    assert all(any((1 << i) & v for v in witnesses) for i in range(2*N))
    return order, parents, maximal, witnesses


if __name__ == "__main__":
    order, parents, maximal, witnesses = certificate()
    print("ordered vertices:", order)
    print("parents of vertices 8 through 25, in the new numbering:", parents)
    print("maximal independent masks of the 8-cycle:", maximal)
    print("generic witnesses (original vertex masks):", witnesses)
    print("witness point masks:", [r & ((1 << N)-1) for r in witnesses])
