"""Classify two-gate Heawood prefixes that survive boundary replacement.

python3 heawood_shards.py --json produces reproducible representatives.
Wire 14 denotes the first gate when it is an operand of the second gate.
"""
import argparse
from collections import Counter
from itertools import combinations
import json

from heawood_prefix import FULL, INPUT, NEGATIVE, POSITIVE, TARGET, VERTICES, symmetry_group


def gated(pool):
    for a, b in combinations(range(len(pool)), 2):
        yield (0, a, b), pool[a] & pool[b]
        yield (1, a, b), pool[a] | pool[b]


def replaceable(value, other):
    # Old -> replacement on minimal true rows. Replacement -> old on maximal false rows.
    return not ((value & ~other & TARGET) | (other & ~value & (FULL ^ TARGET)))


def image(g, perm):
    op, a, b = g
    a, b = (perm[i] if i < 14 else 14 for i in (a, b))
    return op, min(a, b), max(a, b)


def classes(items, group):
    unseen = set(items)
    classes = []
    while unseen:
        prefix = min(unseen)
        orbit = set()
        for permutation in group:
            mapped = tuple(image(g, permutation) for g in prefix)
            orbit.add(mapped)
            if len(mapped) == 2 and 14 not in mapped[1][1:]:
                orbit.add(mapped[::-1])
        # When independent gates can exchange order, survival must be tested in
        # that order too. The intersection keeps exactly the surviving orders.
        orbit.intersection_update(items)
        assert orbit <= unseen
        unseen.difference_update(orbit)
        classes.append((prefix, len(orbit)))
    return classes


def main(as_json):
    assert (len(POSITIVE), len(NEGATIVE)) == (21, 37)
    group = symmetry_group()
    first, second = set(), set()
    for gate1, value1 in gated(INPUT):
        if any(replaceable(value1, s) for s in [*INPUT, 0, FULL]):
            continue
        first.add((gate1,))
        pool = INPUT + [value1]
        for gate2, value2 in gated(pool):
            if any(replaceable(value2, s) for s in [*pool, 0, FULL]):
                continue
            # An independent second gate can also replace the first everywhere
            # in the continuation. Both can be computed in either order.
            if 14 not in gate2[1:] and replaceable(value1, value2):
                continue
            second.add((gate1, gate2))
    one = classes(first, group)
    two = classes(second, group)
    assert sum(n for _, n in one) == len(first)
    assert sum(n for _, n in two) == len(second)
    if as_json:
        print(json.dumps({"gate_ops": ["and", "or"], "one": one, "two": two}, indent=2))
    else:
        print(f"first gates: {len(first)} survivors, {len(one)} orbits")
        print(f"two-gate prefixes: {len(second)} ordered survivors, {len(two)} orbits")
        print("first gate representatives and populations:", one)
        print("two-gate orbit counts by dependency and gate operations:",
              sorted(Counter((14 in p[1][1:], p[0][0], p[1][0]) for p, _ in two).items()))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    main(parser.parse_args().json)
