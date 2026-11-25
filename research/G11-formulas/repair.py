"""Compute optimal vertex-cover repairs for every deletion of G11 edges."""
from collections import Counter
from pathlib import Path
import json
import sys

EDGES = [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
         (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]


def all_repairs():
    vertex_masks = [(1 << a) | (1 << b) for a, b in EDGES]
    missed = [sum(1 << j for j, e in enumerate(vertex_masks) if not x & e)
              for x in range(1 << 11)]
    covers = [x for x, m in enumerate(missed) if m == 0]
    min_full = min(x.bit_count() for x in covers)
    values = [None] * (1 << len(EDGES))
    for x, removed in enumerate(missed):
        repair, y = min(((z & ~x).bit_count(), z) for z in covers if (x & z) == x)
        candidate = (x.bit_count(), repair, x, y)
        if values[removed] is None or candidate < values[removed]:
            values[removed] = candidate
    for j in range(len(EDGES)):
        bit = 1 << j
        for mask in range(len(values)):
            if mask & bit:
                subset = values[mask ^ bit]
                if subset is not None and (values[mask] is None or subset < values[mask]):
                    values[mask] = subset
    return min_full, values


def summarize():
    min_full, answers = all_repairs()
    extra = Counter()
    repairs = Counter()
    by_count = {}
    exceptions = []
    for mask, (residual, repair, x, y) in enumerate(answers):
        k = mask.bit_count()
        excess = residual + repair - min_full
        assert 0 <= excess and repair <= k and (y & x) == x
        extra[excess] += 1
        repairs[repair] += 1
        by_count.setdefault(k, Counter())[repair] += 1
        if excess:
            exceptions.append(dict(removed=f"{mask:04x}", residual=residual, repair=repair,
                                   residual_cover=x, repaired_cover=y))
    assert crosscheck(min_full, answers, exceptions) == Counter({0:65519, 1:17})
    return dict(cover_number=min_full, extra=dict(sorted(extra.items())), repair_distribution=dict(sorted(repairs.items())),
                by_deleted_size={k:dict(sorted(v.items())) for k,v in sorted(by_count.items())}, exceptions=exceptions)


def crosscheck(min_full, answers, records):
    """Represent all deletion sets as bits. Group covers by residual and repaired sizes."""
    n = 11
    edge_sets = 1 << len(EDGES)
    all_sets = (1 << edge_sets) - 1
    # Bit i in this truth column says deletion set i contains edge j.
    contains = []
    for j in range(len(EDGES)):
        run = 1 << j
        low = (1 << run) - 1
        contains.append((all_sets // ((1 << (2 * run)) - 1)) * (low << run))
    covers = []
    grouped = {}
    masks = [(1 << i) | (1 << j) for i,j in EDGES]
    for x in range(1 << n):
        if all(x & e for e in masks):
            covers.append(x)
    minimal = [c for c in covers if all((c & ~bit) not in covers for bit in (1 << v for v in range(n) if c >> v & 1))]
    for x in range(1 << n):
        valid = all_sets
        for e, bitset in zip(masks, contains):
            if not x & e:
                valid &= bitset
        key = (x.bit_count(), min((x | y).bit_count() for y in minimal))
        grouped[key] = grouped.get(key, 0) | valid
    used = 0
    totals = Counter()
    exceptional = 0
    expected = {}
    for mask, (cost, add, _, _) in enumerate(answers):
        key = (cost, cost + add)
        if key not in expected:
            expected[key] = bytearray(edge_sets // 8)
        expected[key][mask // 8] |= 1 << (mask % 8)
    for (cost, end), feasible in sorted(grouped.items()):
        first = feasible & ~used
        assert first == int.from_bytes(expected.pop((cost, end), b""), "little")
        totals[end - min_full] += first.bit_count()
        used |= feasible
        if end > min_full:
            exceptional |= first
    assert used == all_sets
    assert not expected
    assert exceptional == sum(1 << int(row["removed"], 16) for row in records)
    return +totals


if __name__ == "__main__":
    out = summarize()
    if len(sys.argv) > 1:
        Path(sys.argv[1]).write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print("global cover", out["cover_number"], "extension excess", out["extra"], "repair counts", out["repair_distribution"])
    print("by size", out["by_deleted_size"])
    print("exceptional masks", [r["removed"] for r in out["exceptions"]])
