"""Remove a gate by selecting one of its inputs, then resynthesize a second gate.

For each remaining gate all acyclic sources and both binary monotone operations
are considered. An exact check uses every minimal positive and maximal negative.
"""
from argparse import ArgumentParser
from itertools import combinations
from pathlib import Path
import json
from random import Random
from time import monotonic

from plane_search import N, boundary, columns, evaluate, replace, star_cover


def repair(gates, inputs, samples, target, exact, max_size):
    n = 2 * N
    vals = evaluate(gates, inputs)
    errors = vals[-1] ^ target
    if errors == 0 and evaluate(gates, exact)[-1] == target:
        return gates
    care = [0] * len(vals)
    care[-1] = (1 << samples) - 1
    sources_of = [0] * n
    for i, (_, a, b) in enumerate(gates, n):
        sources_of.append((1 << i) | sources_of[a] | sources_of[b])
    for i in reversed(range(n, len(vals))):
        op, a, b = gates[i - n]
        care[a] |= care[i] & (vals[b] if op == "and" else ~vals[b])
        care[b] |= care[i] & (vals[a] if op == "and" else ~vals[a])
    for root in reversed(range(n, len(vals))):
        observable = care[root]
        if errors & ~observable:
            continue
        ones = observable & target
        zeros = observable & ~target
        wires = [s for s in range(len(vals)) if not ((sources_of[s] >> root) & 1)]

        def check(expr):
            candidate = replace(gates, root, expr)
            return candidate if len(candidate) <= max_size and evaluate(candidate, exact)[-1] == target else None

        for s in wires:
            if not (vals[s] ^ target) & observable:
                answer = check(s)
                if answer:
                    return answer
        for op in ("and", "or"):
            if op == "and":
                viable = [s for s in wires if not ones & ~vals[s]]
            else:
                viable = [s for s in wires if not zeros & vals[s]]
            for a, b in combinations(viable, 2):
                if op == "and":
                    works = not (vals[a] & vals[b] & zeros)
                else:
                    works = not (ones & ~(vals[a] | vals[b]))
                if works:
                    answer = check((op, a, b))
                    if answer:
                        return answer
    return None


def main():
    cli = ArgumentParser()
    cli.add_argument("--seeds", type=int, default=4)
    cli.add_argument("--out", type=Path)
    cli.add_argument("--self-test", action="store_true")
    args = cli.parse_args()
    positive, negative = boundary()
    target = (1 << len(positive)) - 1
    exact = columns(positive + negative)
    sample_rows = positive + Random(56107).sample(negative, 1536)
    select = columns(sample_rows)
    if args.self_test:
        damaged = star_cover(0)
        _, a, b = damaged[0]
        damaged[0] = ("and", a, b)
        assert evaluate(damaged, exact)[-1] != target
        fixed = repair(damaged, select, len(sample_rows), target, exact, 125)
        assert fixed and evaluate(fixed, exact)[-1] == target
        print("Checked detection and repair of a planted gate error", flush=True)
        return
    eliminated = 0
    for seed in range(args.seeds):
        t = monotonic()
        baseline = star_cover(seed)
        for i, (_, a, b) in enumerate(baseline, 2 * N):
            for src in [a, b]:
                damaged = replace(baseline, i, src)
                answer = repair(damaged, select, len(sample_rows), target, exact, 124)
                if answer:
                    if args.out:
                        args.out.write_text(json.dumps(answer), encoding="utf-8")
                    print("Found", len(answer), "gates in seed", seed, flush=True)
                    return
                eliminated += 1
        print(f"seed {seed}: {eliminated} deletion cases cumulatively, no repair ({monotonic()-t:.1f}s)", flush=True)


if __name__ == "__main__":
    main()
