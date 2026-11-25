"""Replay finite restriction certificates for the PG(2,3) monotone promise."""
from array import array
from collections import Counter
from functools import cache
from itertools import combinations
from pathlib import Path
import sys

HALF = (1 << 13) - 1
ALL = (1 << 26) - 1
DIFFERENCES = {0, 1, 3, 9}
EDGES = [(p, 13 + l) for p in range(13) for l in range(13) if (p - l) % 13 in DIFFERENCES]
NEIGHBORS = [sum(1 << (q if p == v else p) for p, q in EDGES if v in (p, q)) for v in range(26)]


def bits(mask):
    while mask:
        b = mask & -mask
        yield b
        mask -= b


@cache
def positive(mask):
    return any(mask >> p & mask >> q & 1 for p, q in EDGES)


@cache
def negative(mask):
    return not positive(mask) and all((mask & n).bit_count() <= 2 for n in NEIGHBORS)


def nonconstant(one, free):
    return negative(one) and positive(one | free)


def symmetries():
    result = []
    edge_set = {frozenset(e) for e in EDGES}
    for dual in (False, True):
        for scale in (1, 3, 9):
            for shift in range(13):
                p = [(shift + (-1 if dual else 1) * scale * i) % 13 for i in range(13)]
                full = [p[i % 13] + 13 * ((i < 13) if dual else (i >= 13)) for i in range(26)]
                assert len(set(full)) == 26 and {frozenset((full[u], full[v])) for u, v in EDGES} == edge_set
                lookup = array("H", [0]) * 8192
                for x in range(1, 8192):
                    b = x & -x
                    lookup[x] = lookup[x - b] | (1 << p[b.bit_length() - 1])
                result.append((dual, lookup))
    return result


GROUP = symmetries()
FULL = []


def load_group(path):
    data = Path(path).read_bytes()
    assert len(data) % 26 == 0 and data
    permutations = {data[i:i+26] for i in range(0, len(data), 26)}
    edge_set = {frozenset(e) for e in EDGES}
    for p in sorted(permutations):
        assert set(p) == set(range(26))
        assert {frozenset((p[u], p[v])) for u, v in EDGES} == edge_set
        assert all((p[j] < 13) == (p[0] < 13) for j in range(13))
        FULL.append(tuple(1 << v for v in p))


@cache
def left_images(one):
    occupied = [b.bit_length()-1 for b in bits(one)]
    values = [sum(p[i] for i in occupied) for p in FULL]
    minimum = min(values)
    return minimum, tuple(j for j, value in enumerate(values) if value == minimum)


@cache
def canonical(one, zero):
    if FULL:
        first, choices = left_images(one)
        occupied = [b.bit_length()-1 for b in bits(zero)]
        return first, min(sum(FULL[j][i] for i in occupied) for j in choices)
    def image(x, flip, row):
        lo, hi = row[x & HALF], row[x >> 13]
        return (hi | (lo << 13)) if flip else (lo | (hi << 13))
    return min((image(one, f, row), image(zero, f, row)) for f, row in GROUP)


def support(one, free):
    found = 0
    for p in bits(free):
        for ctx in [0, *bits(free ^ p)]:
            if negative(one | ctx) and positive(one | ctx | p):
                found |= p
                break
    return found


def no_funnel(one, free, p, q):
    values = (0, p, q, p | q)
    open_triples = set(combinations(range(4), 3))
    for ctx in [0, *bits(free ^ (p | q))]:
        rows = [one | ctx | r for r in values]
        open_triples = {t for t in open_triples if not (
            any(positive(rows[i]) for i in t) and any(negative(rows[i]) for i in t))}
        if not open_triples:
            return True
    return False


def core_bound(one, free, seed):
    assert seed and not (seed & ~free)
    vertices = list(bits(seed))
    degree = [(NEIGHBORS[b.bit_length()-1] & seed).bit_count() for b in vertices]
    covered = vertices[0]
    for _ in vertices:
        covered |= sum(b for b in vertices if not b & covered and NEIGHBORS[b.bit_length()-1] & covered)
    assert covered == seed
    if all(d == 2 for d in degree):
        assert len(vertices) >= 5
        complexity = len(vertices) + (len(vertices) + 1) // 2 - 1
    else:
        assert degree.count(1) == 2 and all(d in (1, 2) for d in degree)
        complexity = len(vertices) + len(vertices) // 2 - 2
    # Test every row, including nonmaximal independent sets.
    for i in range(1 << len(vertices)):
        ctx = sum(b for j, b in enumerate(vertices) if (i >> j) & 1)
        assert positive(one | ctx) if positive(ctx) else negative(one | ctx)
    placed = seed
    while placed != free:
        old = placed
        for v in bits(free ^ placed):
            if any(negative(one | u) and positive(one | u | v) for u in bits(placed)):
                placed |= v
        assert placed != old
    return complexity + (free ^ seed).bit_count()


def replay(path):
    rows = {}
    for line in Path(path).read_text().splitlines():
        one, zero, bound, rule, arg = map(int, line.split())
        assert not one & zero and 0 <= (one | zero) <= ALL and canonical(one, zero) == (one, zero)
        assert (one, zero) not in rows
        rows[one, zero] = (bound, rule, arg)
    seen = set()

    def check(one, zero, need):
        if need <= 0:
            return
        key = canonical(one, zero)
        k, rule, arg = rows[key]
        assert k >= need
        if key in seen:
            return
        seen.add(key)
        one, zero = key
        free = ALL ^ (one | zero)
        assert nonconstant(one, free)
        if rule == 1:
            assert arg & ~support(one, free) == 0 and k <= arg.bit_count() - 1
        elif rule == 2:
            assert k <= core_bound(one, free, arg)
        elif rule == 3:
            assert arg and not arg & ~free and nonconstant(one, free ^ arg)
            assert all(positive(one | p) for p in bits(arg))
            check(one, zero | arg, k - arg.bit_count())
        elif rule == 4:
            assert support(one, free)
            assert all(nonconstant(one | v, free ^ v) and nonconstant(one, free ^ v) for v in bits(free))
            assert all(no_funnel(one, free, p, q) for p, q in combinations(bits(free), 2))
            for v in bits(free):
                check(one, zero | v, k - 3)
                check(one | v, zero, k - 4)
        elif rule in (5, 6):
            assert arg.bit_count() == 1 and arg & support(one, free)
            o, z = (one, zero | arg) if rule == 5 else (one | arg, zero)
            assert nonconstant(o, ALL ^ (o | z))
            check(o, z, k - 1)
        elif rule == 7:
            assert arg.bit_count() == 1 and arg & support(one, free)
            assert nonconstant(one, free ^ arg) and nonconstant(one | arg, free ^ arg)
            check(one, zero | arg, k - 2)
            check(one | arg, zero, k - 2)
        else:
            raise ValueError(rule)
    root = rows[0, 0][0]
    check(0, 0, root)
    assert len(seen) == len(rows)
    print("lower", root, "checked states", len(seen), "rule counts",
          sorted(Counter(r[1] for r in rows.values()).items()), flush=True)


if __name__ == "__main__":
    args = sys.argv[1:]
    if args[:1] == ["--group"]:
        load_group(args[1])
        args = args[2:]
    for file in args:
        replay(file)
