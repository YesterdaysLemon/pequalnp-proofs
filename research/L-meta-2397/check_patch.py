"""Evaluate a synthesized replacement and all untouched stars against the plane."""
from itertools import combinations
from pathlib import Path
import sys


def subsets():
    for size in range(14):
        yield from map(frozenset, combinations(range(13), size))


def check(centers, path):
    centers = tuple(centers)
    incident = lambda p, l: (p-l) % 13 in (0, 1, 3, 9)
    points_on = [{p for p in range(13) if incident(p, l)} for l in range(13)]
    through = [{l for l in range(13) if incident(p, l)} for p in range(13)]
    classes = {}
    for l, points in enumerate(points_on):
        seen = frozenset(points.intersection(centers))
        if seen:
            classes.setdefault(seen, []).append(l)
    gates = []
    trace = Path(path).read_text().splitlines()
    assert trace[-1].startswith("SAT ")
    for s in trace[:-1]:
        index, eq, op, a, b = s.split()
        assert int(index) == len(centers)+len(classes)+len(gates) and eq == "=" and op in "&|"
        assert 0 <= int(a) < int(index) and 0 <= int(b) < int(index)
        gates.append((op,int(a),int(b)))
    charged = sum(len(v)-1 for v in classes.values())
    total = (13-len(centers))*4 + (13-len(centers)) + charged + len(gates)
    def evaluate(points, lines):
        if any(points_on[l] & points - set(centers) for l in lines):
            return True
        wires = [v in points for v in centers] + [any(l in lines for l in group) for group in classes.values()]
        for op, a, b in gates:
            wires.append(wires[a] and wires[b] if op == "&" else wires[a] or wires[b])
        return wires[-1]
    for p in range(13):
        for l in through[p]:
            assert evaluate({p},{l})
    p_arcs = [s for s in subsets() if all(len(s & ns) <= 2 for ns in points_on)]
    l_arcs = [s for s in subsets() if all(len(s & ns) <= 2 for ns in through)]
    count = 0
    for points in p_arcs:
        allowed = set(range(13)).difference(*(through[p] for p in points))
        for lines in l_arcs:
            if lines <= allowed:
                assert not evaluate(points, lines)
                count += 1
    print(f"{total} gates, 52 flags, {count} independent pairs of arcs checked")


if __name__ == "__main__":
    check(map(int, sys.argv[2:]), sys.argv[1])
