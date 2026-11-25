"""Search for a strictly smaller exact monotone circuit for the order-four plane.

Only the 105 positive edges and the maximal negative inputs need to be tested.
Each initial circuit is a tree above the primary inputs. A gate can be changed
precisely on its observable rows: propagate a care mask from the output, keeping
rows where the other input does not control the value of the parent gate.
"""
from argparse import ArgumentParser
from itertools import combinations
import json
from pathlib import Path
from random import Random
from time import monotonic


N = 21
OFFSETS = (0, 1, 4, 14, 16)
LINES = tuple(tuple((line + delta) % N for delta in OFFSETS) for line in range(N))
POINTS = tuple(tuple(line for line in range(N) if point in LINES[line]) for point in range(N))
FULL = (1 << N) - 1


def boundary():
    masks = [sum(1 << line for line in row) for row in POINTS]
    covered = {0}
    for row in masks:
        covered.update({seen | row for seen in covered})
    positive = [(1 << point) | (1 << (N + line)) for line in range(N) for point in LINES[line]]
    negative = []
    for covered_lines in sorted(covered):
        remaining_lines = FULL ^ covered_lines
        maximal_points = sum(1 << p for p, row in enumerate(masks) if not row & remaining_lines)
        negative.append(maximal_points | (remaining_lines << N))
    return positive, negative


def columns(rows):
    packed = [bytearray((len(rows) + 7) // 8) for _ in range(2 * N)]
    for i, row in enumerate(rows):
        while row:
            bit = row & -row
            packed[bit.bit_length() - 1][i // 8] |= 1 << (i % 8)
            row ^= bit
    return [int.from_bytes(x, "little") for x in packed]


def star_cover(seed, redundant=False, mixed=False):
    rng = Random(seed)
    gates = []

    def gate(op, a, b):
        gates.append((op, a, b))
        return 2 * N + len(gates) - 1

    def combine(wires):
        wires = list(wires)
        if seed:
            rng.shuffle(wires)
        while len(wires) > 1:
            a = wires.pop(rng.randrange(len(wires)) if seed else -1)
            b = wires.pop(rng.randrange(len(wires)) if seed else -1)
            wires.append(gate("or", a, b))
        return wires[0]

    centers = list(range(N))
    if seed:
        rng.shuffle(centers)
    dual = seed % 2
    neighborhoods = POINTS if dual else LINES
    moved = {}
    if mixed:
        reverse = LINES if dual else POINTS
        for other in rng.sample(centers, 1 + seed % 3):
            moved[other] = set(rng.sample(reverse[other], rng.randint(2, 5)))
    stars = []
    for center in centers:
        first = center if dual else center + N
        others = (x + N if dual else x for x in neighborhoods[center] if center not in moved.get(x, ()))
        stars.append(gate("and", first, combine(others)))
    for other, members in moved.items():
        first = other + N if dual else other
        others = (x if dual else x + N for x in sorted(members))
        stars.append(gate("and", first, combine(others)))
    output = combine(stars)
    if redundant:
        gate("or", output, output)
    return gates


def evaluate(gates, inputs):
    vals = list(inputs)
    for op, a, b in gates:
        vals.append(vals[a] & vals[b] if op == "and" else vals[a] | vals[b])
    return vals


def replace(gates, root, expr):
    output = []
    saved = {}

    def visit(w):
        if isinstance(w, int) and w < 2 * N:
            return w
        if w in saved:
            return saved[w]
        if w == root:
            return visit(expr)
        op, a, b = w if isinstance(w, tuple) else gates[w - 2 * N]
        left, right = visit(a), visit(b)
        out = 2 * N + len(output)
        output.append((op, left, right))
        saved[w] = out
        return out

    last = visit(2 * N + len(gates) - 1)
    assert last == 2 * N + len(output) - 1
    return output


def search(gates, inputs, total, desired, max_new, validate, max_size):
    start = 2 * N
    vals = evaluate(gates, inputs)
    assert vals[-1] == desired
    care = [0] * len(vals)
    care[-1] = (1 << total) - 1
    cone = [0] * start
    for i, (op, a, b) in enumerate(gates, start):
        cone.append(cone[a] | cone[b] | (1 << i))
    for i in reversed(range(start, len(vals))):
        op, a, b = gates[i - start]
        care[a] |= care[i] & (vals[b] if op == "and" else ~vals[b])
        care[b] |= care[i] & (vals[a] if op == "and" else ~vals[a])

    for root in reversed(range(start, len(vals))):
        wanted = care[root] & vals[root]
        forbidden = care[root] & ~vals[root]
        sources = [s for s in range(len(vals)) if not (cone[s] >> root) & 1]
        available = cone[root]

        def try_it(expr):
            candidate = replace(gates, root, expr)
            if len(candidate) <= max_size and validate(candidate):
                return candidate
            return None

        for s in sources:
            if not ((vals[s] ^ vals[root]) & care[root]):
                candidate = try_it(s)
                if candidate is not None:
                    return candidate

        def inner(must_one, must_zero, budget, outer_cone=0):
            for op in ("and", "or"):
                if op == "and":
                    allowed = [s for s in sources if not must_one & ~vals[s]]
                else:
                    allowed = [s for s in sources if not must_zero & vals[s]]
                for a, b in combinations(allowed, 2):
                    if (available & ~(outer_cone | cone[a] | cone[b])).bit_count() <= budget:
                        continue
                    if op == "and":
                        ok = not (vals[a] & vals[b] & must_zero)
                    else:
                        ok = not (must_one & ~(vals[a] | vals[b]))
                    if ok:
                        yield (op, a, b)

        if max_new >= 1 and available.bit_count() >= 2:
            for expr in inner(wanted, forbidden, 1):
                candidate = try_it(expr)
                if candidate is not None:
                    return candidate
        if max_new >= 2 and available.bit_count() >= 3:
            for outer in ("and", "or"):
                for s in sources:
                    if outer == "and":
                        if wanted & ~vals[s]:
                            continue
                        one, zero = wanted, forbidden & vals[s]
                    else:
                        if forbidden & vals[s]:
                            continue
                        one, zero = wanted & ~vals[s], forbidden
                    for expr in inner(one, zero, 2, cone[s]):
                        candidate = try_it((outer, s, expr))
                        if candidate is not None:
                            return candidate
    return None


def main():
    cli = ArgumentParser()
    cli.add_argument("--seeds", type=int, default=2)
    cli.add_argument("--first", type=int, default=0)
    cli.add_argument("--max-new", type=int, choices=[0, 1, 2], default=2)
    cli.add_argument("--redundant", action="store_true")
    cli.add_argument("--mixed", action="store_true")
    cli.add_argument("--max-size", type=int)
    cli.add_argument("--out", type=Path)
    args = cli.parse_args()
    positive, negative = boundary()
    target = (1 << len(positive)) - 1
    exact = columns(positive + negative)
    small = positive + Random(56107).sample(negative, min(1536, len(negative)))
    partial = columns(small)
    print(f"{len(positive)} positive rows, {len(negative)} maximal negative rows", flush=True)
    for seed in range(args.first, args.first + args.seeds):
        t = monotonic()
        gates = star_cover(seed, args.redundant, args.mixed)
        limit = len(gates) - 1 if args.max_size is None else min(len(gates) - 1, args.max_size)
        assert evaluate(gates, exact)[-1] == target
        answer = search(gates, partial, len(small), target, args.max_new,
                        lambda c: evaluate(c, exact)[-1] == target, limit)
        if answer is not None:
            print(f"seed {seed}: {len(gates)} -> {len(answer)} gates", flush=True)
            if args.out:
                args.out.write_text(json.dumps(answer), encoding="utf-8")
            return
        print(f"seed {seed}: no circuit of size <= {limit} with up to {args.max_new} new gates ({monotonic()-t:.2f}s)", flush=True)


if __name__ == "__main__":
    main()
