"""Exhaustive three-gate completions of six full Heawood stars, up to symmetry."""
from functools import reduce
from itertools import combinations, permutations
from operator import or_
import argparse


ADJACENCY = (1408, 8832, 12544, 6272, 11264, 5632, 2816)
VERTICES = tuple(range(14))
NEIGHBORS = [tuple(l for l in range(7, 14) if mask & (1 << l)) for mask in ADJACENCY]
NEIGHBORS += [tuple(p for p in range(7) if l in NEIGHBORS[p]) for l in range(7, 14)]
EDGES = tuple((p, l) for p in range(7) for l in NEIGHBORS[p])
POSITIVE = tuple((1 << p) | (1 << l) for p, l in EDGES)


def collision(row):
    return any(row & (1 << p) and row & mask for p, mask in enumerate(ADJACENCY))


NEGATIVE = tuple(row for row in range(1 << 14) if not collision(row) and
                 all(collision(row | (1 << v)) for v in VERTICES if not row & (1 << v)))
ROWS = POSITIVE + NEGATIVE
TARGET = (1 << len(POSITIVE)) - 1
FULL = (1 << len(ROWS)) - 1
INPUT = [sum(1 << i for i, row in enumerate(ROWS) if row & (1 << v)) for v in VERTICES]


def symmetry_group():
    line_to_vertex = {frozenset(NEIGHBORS[l]): l for l in range(7, 14)}
    dual = tuple(range(7, 14)) + tuple(range(7))
    group = set()
    for mapping in permutations(range(7)):
        images = [frozenset(mapping[p] for p in NEIGHBORS[l]) for l in range(7, 14)]
        if any(image not in line_to_vertex for image in images):
            continue
        perm = mapping + tuple(line_to_vertex[image] for image in images)
        group.add(perm)
        group.add(tuple(dual[x] for x in perm))
    assert len(group) == 336
    assert all({tuple(sorted((perm[p], perm[l]))) for p, l in EDGES} == set(EDGES)
               for perm in group)
    return group


def representatives():
    group = symmetry_group()
    unseen = set(combinations(VERTICES, 6))
    while unseen:
        centers = min(unseen)
        orbit = {tuple(sorted(perm[v] for v in centers)) for perm in group}
        assert orbit <= unseen
        unseen.difference_update(orbit)
        yield centers, len(orbit)


def bank(centers):
    # All side subdisjunctions, including ones absent from a chosen association.
    entries = {val: f"x{v}" for v, val in enumerate(INPUT)}
    entries.update({0: "0", FULL: "1"})
    for center in centers:
        for size in (2, 3):
            for side in combinations(NEIGHBORS[center], size):
                value = reduce(or_, (INPUT[v] for v in side))
                entries[value] = "(" + "|".join(f"x{v}" for v in side) + ")"
    # Any pure output of complete stars can be replaced by H. This can only
    # increase an internal value, and only on positive rows where the target is 1.
    h = sum(1 << i for i, ends in enumerate(EDGES) if set(ends).intersection(centers))
    entries[h] = "H"
    return entries


def first_gates(base):
    wires = dict(base)
    for a, b in combinations(base, 2):
        for symbol, value in (("&", a & b), ("|", a | b)):
            if value not in wires:
                wires[value] = f"({base[a]}{symbol}{base[b]})"
    return wires


def solve(base, target):
    """Every connected DAG with at most three live binary AND/OR gates.

    A gate feeding both another gate and the root is comparable to the
    intervening gate, so their final AND/OR equals one of its two inputs.
    The remaining shapes are parallel one-gate children or a three-gate path.
    """
    first = first_gates(base)
    if target in first:
        return first[target]
    below = [v for v in first if v & target == v]
    above = [v for v in first if v & target == target]
    for candidates, op in ((below, "|"), (above, "&")):
        for a, b in combinations(candidates, 2):
            if (a | b if op == "|" else a & b) == target:
                return f"({first[a]}{op}{first[b]})"
    # In a chain the final gate has one base child and one two-gate child.
    lower_base = [v for v in base if v & target == v]
    upper_base = [v for v in base if v & target == target]
    for a in first:
        for b in base:
            for s, mid in (("&", a & b), ("|", a | b)):
                if mid & target == mid:
                    for c in lower_base:
                        if mid | c == target:
                            return f"(({first[a]}{s}{base[b]})|{base[c]})"
                if mid & target == target:
                    for c in upper_base:
                        if mid & c == target:
                            return f"(({first[a]}{s}{base[b]})&{base[c]})"
    return None


def generic_check():
    # Compare with a direct topological enumeration on small truth tables.
    for base in ({0xAA: "a", 0xCC: "b", 0xF0: "c"},
                 {0x1C: "u", 0x64: "v", 0xAF: "w", 0x32: "x"}):
        all_values = set(base)
        def extend(values, left):
            if left == 0:
                return
            for a, b in combinations(values, 2):
                for v in (a & b, a | b):
                    if v not in values:
                        all_values.add(v)
                        extend(values | {v}, left - 1)
        extend(set(base), 3)
        assert all((solve(base, t) is not None) == (t in all_values) for t in range(256))


def four_gates(base, target):
    short = solve(base, target)
    if short:
        return short
    for value, label in first_gates(base).items():
        if value in base:
            continue
        witness = solve(base | {value: label}, target)
        if witness:
            return witness
    return None


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--four", action="store_true",
                        help="classify four-gate completions as well")
    args = parser.parse_args()
    assert (len(POSITIVE), len(NEGATIVE)) == (21, 37)
    generic_check()
    positive_control = bank(tuple(range(6)))
    missing = INPUT[6] & reduce(or_, (INPUT[v] for v in NEIGHBORS[6]))
    h = next(k for k, name in positive_control.items() if name == "H")
    assert h | missing == TARGET
    counts = [0, 0]
    accepted = []
    at_four = []
    for centers, population in representatives():
        base = bank(centers)
        witness = solve(base, TARGET)
        counts[0] += 1
        counts[1] += population
        print(centers, population, len(base), witness or "none", flush=True)
        if witness:
            accepted.append((centers, witness))
        if args.four:
            extra = four_gates(base, TARGET)
            print("four:", centers, extra or "none", flush=True)
            if extra:
                at_four.append((centers, population, extra))
    assert counts[1] == 3003
    print(f"{counts[0]} orbits, {counts[1]} center sets, {len(accepted)} possible completions")
    if args.four:
        print("four-gate completions:", len(at_four), "orbits,",
              sum(k for _, k, _ in at_four), "center sets")
