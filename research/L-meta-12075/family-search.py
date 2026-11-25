"""Classify monotone six-input extensions of the common five-input cofactor."""
import argparse
import itertools
import json
import re
import subprocess
from pathlib import Path

HIGH = 0xFE80E800
DATA = (0, 1, 2, 4)


def relabel(word, permutation):
    result = 0
    for row in range(32):
        relabeled = row & 8
        for src, dst in zip(DATA, permutation):
            relabeled |= (row >> src & 1) << dst
        result |= (word >> row & 1) << relabeled
    return result


def classes():
    words = [0, 1]
    for n in range(5):
        words = [a | (b << (1 << n)) for b in words for a in words if a & ~b == 0]
    remaining = {w for w in words if w & ~HIGH == 0 and w != HIGH}
    assert len(words) == 7581
    answer = {}
    while remaining:
        low = min(remaining)
        orbit = {relabel(low, p) for p in itertools.permutations(DATA)}
        assert orbit <= remaining
        remaining -= orbit
        answer[f"{low:08x}"] = len(orbit)
    return answer


def verify(low, gates):
    target = (HIGH << 32) | low
    for x in range(64):
        values = [bool(x >> i & 1) for i in range(6)]
        for op, a, b in gates:
            assert 0 <= a < len(values) and 0 <= b < len(values)
            values.append((values[a] and values[b]) if op == "&" else (values[a] or values[b]))
        assert values[-1] == bool(target >> x & 1)


def search(exe, low, size, cap):
    process = subprocess.run([exe, low, "-1", str(size), "0", str(cap)], check=True,
                             text=True, capture_output=True)
    pattern = r"^(SAT|UNSAT|UNKNOWN) binary \d+ available NOT 0 free signs 0 visits (\d+)"
    verdict = re.search(pattern, process.stdout, re.MULTILINE)
    assert verdict is not None, process.stdout
    result = {"verdict": verdict[1], "visits": int(verdict[2])}
    if verdict[1] == "SAT":
        gates = [(op, int(a), int(b)) for _, op, a, b in
                 re.findall(r"^(\d+) = ([&|]) (\d+) (\d+)$", process.stdout, re.MULTILINE)]
        assert len(gates) <= size
        verify(int(low, 16), gates)
        result["gates"] = gates
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--search", type=str)
    parser.add_argument("--node-limit", type=int, default=500000)
    parser.add_argument("--budget", type=int, choices=(10,11), default=11)
    parser.add_argument("--results", type=Path)
    args = parser.parse_args()
    orbits = classes()
    results = {}
    if args.results and args.results.exists():
        results = json.loads(args.results.read_text())
    for low, size in orbits.items():
        r = results.setdefault(low, {"multiplicity": size})
        assert r["multiplicity"] == size
        for k, record in r.items():
            if isinstance(record, dict) and record["verdict"] == "SAT":
                verify(int(low, 16), record["gates"])
        key = str(args.budget)
        old = r.get(key, {})
        if args.search and (not old or (old["verdict"] == "UNKNOWN" and old["visits"] < args.node_limit)):
            r[key] = search(args.search, low, args.budget, args.node_limit)
            print(low, size, key, r[key]["verdict"], r[key]["visits"], flush=True)
            if args.results:
                args.results.write_text(json.dumps(results, indent=2) + "\n")
    print(f"{len(orbits)} classes, {sum(orbits.values())} essential monotone extensions")
    for budget in ("10", "11"):
        for verdict in ("SAT", "UNSAT", "UNKNOWN"):
            group = [r for r in results.values() if r.get(budget, {}).get("verdict") == verdict]
            print(budget, verdict, len(group), sum(r["multiplicity"] for r in group))
