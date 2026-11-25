"""Independent truth-table and exact small-circuit checks, using only Python."""
from functools import lru_cache
from itertools import combinations, product


def circuit(n):
    gates = []

    def add(op, left, right):
        gates.append((op, left, right))
        return 2 * n + len(gates) - 1

    conjunction = 0
    for i in range(1, n - 1):
        conjunction = add("&", conjunction, 2 * i)
    last = n - 1
    out = add("&", 2 * last, add("|", 2 * last + 1, conjunction))
    for i in range(last):
        out = add("|", out, add("&", 2 * i, 2 * i + 1))
    return gates, out


def evaluate(n, row):
    pairs = [(row >> (2 * i) & 1, row >> (2 * i + 1) & 1) for i in range(n)]
    return int(all(a for a, _ in pairs) or any(a and b for a, b in pairs))


def check_circuit(n):
    gates, out = circuit(n)
    assert len(gates) == 3 * n - 2
    for row in range(1 << (2 * n)):
        values = [row >> k & 1 for k in range(2 * n)]
        for op, a, b in gates:
            v, w = values[a], values[b]
            values.append(v & w if op == "&" else v | w)
        assert values[out] == evaluate(n, row)
    return len(gates)


def cofactor_counts():
    counts = {}
    for p, q in combinations(range(4), 2):
        rest = [r for r in range(4) if r not in (p, q)]
        residuals = set()
        for a, b in product(range(2), repeat=2):
            residuals.add(tuple(
                evaluate(2, a << p | b << q | u << rest[0] | v << rest[1])
                for u, v in product(range(2), repeat=2)
            ))
        counts[p, q] = len(residuals)
    assert min(counts.values()) >= 3
    return counts


def small_lower(n):
    # Normalize each truth table by complementing its output at row zero.
    rows = 1 << (2 * n)
    mask = (1 << rows) - 1
    target = sum(evaluate(n, i) << i for i in range(rows))
    if target & 1:
        target ^= mask
    primaries = tuple(sum(((i >> j) & 1) << i for i in range(rows)) for j in range(2 * n))
    for j in range(2 * n):
        assert any(evaluate(n, r) != evaluate(n, r ^ (1 << j)) for r in range(rows))

    @lru_cache(maxsize=8192)
    def separates(bank):
        parts = [mask]
        for u in bank:
            parts = [s for p in parts for s in (p & u, p & ~u) if s]
        return all(not (p & target) or not (p & ~target) for p in parts)

    @lru_cache(maxsize=32768)
    def possible(bank, remaining):
        if target in bank:
            return True
        if remaining == 0 or len(bank) > remaining + 1 or not separates(bank):
            return False
        for i, j in combinations(range(len(bank)), 2):
            a, b = bank[i], bank[j]
            rest = [u for k, u in enumerate(bank) if k != i and k != j]
            for z in {a & b, a | b, a & ~b, b & ~a, a ^ b}:
                if not z or z in bank:
                    continue
                for keep in ([], [a], [b], [a, b]):
                    if len(rest) + 1 + len(keep) > remaining:
                        continue
                    nxt = tuple(sorted(rest + [z] + keep))
                    if possible(nxt, remaining - 1):
                        return True
        return False

    budget = 3 * n - 3
    assert not possible(tuple(sorted(primaries)), budget)
    return budget, possible.cache_info().misses


def posted_table():
    # The desk lists the a inputs first and their b partners in reverse order.
    def interleaved(row):
        return sum(
            (((row >> old) & 1) << new)
            for new, old in enumerate([0, 5, 1, 4, 2, 3])
        )

    table = sum(evaluate(3, interleaved(row)) << row for row in range(64))
    assert table == 4277074602 * 2**32 + 4241289344
    return hex(table)


if __name__ == "__main__":
    print("Distinct cofactors by input pair for n=2", cofactor_counts())
    for n in range(2, 9):
        print("Verified monotone circuit", n, check_circuit(n), "gates")
    for n in (2, 3):
        budget, calls = small_lower(n)
        print("Full binary basis, free complements", n, "excluded budget", budget, "states", calls)
    print("Posted six-input table", posted_table())
