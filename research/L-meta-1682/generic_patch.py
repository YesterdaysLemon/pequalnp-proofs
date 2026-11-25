"""Synthesize a smaller circuit for a group of order-three point stars.

The point centers are inputs. Lines with the same nonempty set of selected
neighbors use one disjunction, charged separately. All other point stars
remain in the old formula. A successful local replacement saves a real gate.
"""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from itertools import combinations


N = 13
UNIV = (1 << N) - 1
LINE = [sum(1 << ((l+d) % N) for d in (0, 1, 3, 9)) for l in range(N)]
THROUGH = [sum(1 << l for l in range(N) if LINE[l] >> p & 1) for p in range(N)]


def generic():
    rows = []
    for points in range(1 << N):
        lines = sum(1 << l for l, pts in enumerate(LINE) if not points & pts)
        closed = all((points >> p & 1) or THROUGH[p] & lines for p in range(N))
        if (closed and all(points & ~l for l in LINE) and
                all(lines & ~through for through in THROUGH)):
            rows.append((points, lines))
    assert Counter((x.bit_count(), y.bit_count()) for x, y in rows) == {(3,4):234,(4,3):234}
    return rows


def antichain(masks, minimal):
    sequence = sorted(set(masks), key=int.bit_count, reverse=not minimal)
    result = []
    for x in sequence:
        if not any(x & y == (y if minimal else x) for y in result):
            result.append(x)
    return result


def patch(centers):
    groups = defaultdict(list)
    for l in range(N):
        pattern = sum(1 << i for i, c in enumerate(centers) if LINE[l] >> c & 1)
        if pattern:
            groups[pattern].append(l)
    width = len(centers) + len(groups)
    charged = sum(len(group)-1 for group in groups.values())
    budget = 5 * len(centers) - 2 - charged
    columns = [(1 << p, 0) for p in centers]
    columns += [(0, sum(1 << l for l in group)) for group in groups.values()]
    def project(points, lines):
        return sum(1 << i for i, (p, l) in enumerate(columns) if (points & p) or (lines & l))
    pos = antichain((project(1 << p, 1 << l) for p in centers for l in range(N)
                    if LINE[l] >> p & 1), True)
    neg = antichain((project(p, l) for p, l in generic()), False)
    assert all(p & q != p for p in pos for q in neg)
    return width, charged, budget, pos, neg, columns


def synthesise(width, gates, positives, negatives, conflict_budget):
    from pysat.solvers import Solver
    from pysat.formula import IDPool

    rows = [(p, True) for p in positives] + [(n, False) for n in negatives]
    ids, clauses = IDPool(), []
    sources, ops, values = [], [], []
    for j in range(gates):
        size = width+j
        op = ids.id(("AND",j))
        ops.append(op)
        selectors = [[ids.id(("source",j,side,k)) for k in range(size)] for side in range(2)]
        sources.append(selectors)
        for choices in selectors:
            clauses.append(choices)
            clauses.extend([-u,-v] for u,v in combinations(choices,2))
        for a in range(size):
            for b in range(a+1):
                clauses.append([-selectors[0][a],-selectors[1][b]])
        output = []
        for row, (mask, target) in enumerate(rows):
            sides = [ids.id(("read",j,side,row)) for side in range(2)]
            for side, read in enumerate(sides):
                for k, sel in enumerate(selectors[side]):
                    if k < width:
                        clauses.append([-sel, read if mask >> k & 1 else -read])
                    else:
                        prev = values[k-width][row]
                        clauses.extend(([-sel,-read,prev],[-sel,read,-prev]))
            a,b = sides
            out = ids.id(("out",j,row))
            output.append(out)
            clauses.extend(([-op,-out,a],[-op,-out,b],[-op,out,-a,-b],
                            [op,out,-a],[op,out,-b],[op,-out,a,b]))
            if j == gates-1:
                clauses.append([out if target else -out])
        values.append(output)
    # All gates are live in a circuit of minimum size. Each essential input must
    # occur. Test essentiality directly on observed positive/negative rows.
    for i in range(width):
        essential = any((p & ~n) == (1 << i) for p in positives for n in negatives)
        if essential:
            clauses.append([s[side][i] for s in sources for side in range(2)])
    for j in range(gates-1):
        clauses.append([s[side][width+j] for s in sources[j+1:] for side in range(2)])
    with Solver(name="cadical195", bootstrap_with=clauses) as solver:
        if conflict_budget:
            solver.conf_budget(conflict_budget)
        sat = solver.solve_limited()
        if sat is not True:
            return ("UNSAT" if sat is False else "UNKNOWN"), solver.accum_stats()["conflicts"]
        model = set(solver.get_model())
    result = []
    for op, choices in zip(ops, sources):
        a,b = [next(k for k, sel in enumerate(side) if sel in model) for side in choices]
        result.append(("and" if op in model else "or",a,b))
    for mask, target in rows:
        wires = [bool(mask >> k & 1) for k in range(width)]
        for op,a,b in result:
            wires.append(wires[a] and wires[b] if op == "and" else wires[a] or wires[b])
        assert wires[-1] == target
    return "SAT", result


if __name__ == "__main__":
    p = ArgumentParser(description=__doc__)
    p.add_argument("centers", nargs="+", type=int)
    p.add_argument("--conflicts", type=int, default=80000)
    p.add_argument("--extra", type=int, default=0, help="allow more gates, e.g. 1 for a control")
    a = p.parse_args()
    width, charged, budget, pos, neg, columns = patch(a.centers)
    print(f"centers {a.centers} inputs {width} prepaid gates {charged} test size {budget+a.extra} "
          f"minimal positives {len(pos)} maximal negatives {len(neg)}", flush=True)
    print(synthesise(width,budget+a.extra,pos,neg,a.conflicts),flush=True)
