"""Independently check the extremal test inputs by scanning every point subset."""
from array import array

from plane_search import boundary


def unions(neighborhoods):
    out = array("I", [0]) * (1 << len(neighborhoods))
    for mask in range(1, len(out)):
        bit = mask & -mask
        out[mask] = out[mask ^ bit] | neighborhoods[bit.bit_length() - 1]
    return out


def main():
    n = 21
    full = (1 << n) - 1
    flags = [(p, l) for p in range(n) for l in range(n) if (p - l) % n in {0, 1, 4, 14, 16}]
    through = unions([sum(1 << l for u, l in flags if u == p) for p in range(n)])
    on_line = unions([sum(1 << p for p, v in flags if v == l) for l in range(n)])
    maximal = set()
    for selected, touched in enumerate(through):
        disjoint_lines = full ^ touched
        if (full ^ on_line[disjoint_lines]) == selected:
            maximal.add(selected | (disjoint_lines << n))
    positive, negative = boundary()
    assert set(positive) == {(1 << p) | (1 << (n + l)) for p, l in flags}
    assert len(maximal) == len(negative) and maximal == set(negative)
    print(f"Checked all {full + 1} point subsets: {len(positive)} flags, {len(maximal)} maximal negative inputs")


if __name__ == "__main__":
    main()
