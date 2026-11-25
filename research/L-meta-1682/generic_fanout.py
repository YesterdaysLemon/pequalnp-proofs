"""Check the finite certificates used to lift the cycle bound to 31 gates.

The analytic steps are the project's one-gate elimination lemma, exact cycle
size theorem L106, and three-or-four-gate elimination theorem L107.
"""
from itertools import permutations

from generic_patch import N, generic
from generic_cycle import neighbors


VERTICES = range(2*N)
ALL = (1 << (2*N)) - 1
EDGES = [1 << p | 1 << l for p in range(N) for l in range(N,2*N) if neighbors(p,l)]
NEGATIVES = [p | l << N for p,l in generic()]
PROTOTYPES = {False: [1,14,2,15,3,16,6,18], True: [1,14,2,15,5,18]}


def true_row(mask):
    return any(mask & e == e for e in EDGES)


def false_row(mask):
    return any(mask & n == mask for n in NEGATIVES)


def move(v, fixed):
    # Rotation, composed with the point-line duality p <-> -p if needed.
    if fixed >= N:
        v = (N if v < N else 0) + (-v) % N
    return (N if v >= N else 0) + (v + fixed) % N


def restricted_cycle(fixed, value):
    ones = 1 << fixed if value else 0
    order = [move(v,fixed) for v in PROTOTYPES[value]]
    assert 0 <= fixed < 2*N and fixed not in order and len(set(order)) == len(order)
    size = len(order)
    for mask in range(1 << size):
        row = ones | sum(1 << a for i,a in enumerate(order) if mask >> i & 1)
        collision = any((mask >> i) & (mask >> ((i+1)%size)) & 1 for i in range(size))
        assert true_row(row) if collision else false_row(row)
    additions = []
    while len(order) < 2*N-1:
        for v in VERTICES:
            if v == fixed or v in order:
                continue
            for context in [0] + [1 << w for w in order]:
                if false_row(ones | context) and true_row(ones | context | 1 << v):
                    additions.append((v,context))
                    order.append(v)
                    break
            else:
                continue
            break
        else:
            raise AssertionError("no essential vertex to add")
    # Reverse the additions, eliminating the last input at zero one gate at
    # a time. The cycle edge and empty cycle input witness nonconstancy.
    assert true_row(ones | 1 << order[0] | 1 << order[1]) and false_row(ones)
    cycle_size = size + (size+1)//2 - 1
    return cycle_size + len(additions)


def main():
    # With p,q unfixed, context {a} makes the output equal the bit p,
    # independently of q. The reverse order gives a second context reading q.
    # All four two-bit cofactors are consequently distinct.
    for p,q in permutations(VERTICES,2):
        assert any(a not in (p,q) and neighbors(a,p) and false_row(1 << a | 1 << q)
                   for a in VERTICES)
    bounds = {b: [restricted_cycle(v,b) for v in VERTICES] for b in (False,True)}
    print("650 ordered two-coordinate projection witnesses")
    for b in bounds:
        print("fixed", b, "restricted lower bounds", sorted(set(bounds[b])),
              "across",len(bounds[b]),"vertices")
    print("full lower bound by L107:", min(3 + min(bounds[False]), 4 + min(bounds[True])))


if __name__ == "__main__":
    main()
