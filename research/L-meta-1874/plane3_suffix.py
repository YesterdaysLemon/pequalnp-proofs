"""Exhaustively test three binary gates after a prefix computing twelve full stars.

All point/line inputs, constants, and all side disjunctions of each chosen star
are given for free. Prefix wires that combine complete stars can all be replaced
by their total H: this only adds true values on the required positive inputs.
Signatures are evaluated on all flags and all quadrangle inputs of L-meta-1874.
"""
from itertools import combinations
from functools import reduce
from operator import or_


N = 13
D = {0, 1, 3, 9}
LINES = [set((l + d) % N for d in D) for l in range(N)]
FLAGS = [(p, l) for p in range(N) for l in range(N) if p in LINES[l]]
QUADS = [set(q) for q in combinations(range(N), 4) if all(len(set(q) & l) <= 2 for l in LINES)]
ROWS = [(1 << p) | (1 << (N + l)) for p, l in FLAGS]
ROWS += [sum(1 << p for p in q) | sum(1 << (N + l) for l in range(N) if not q & LINES[l]) for q in QUADS]
POS = (1 << len(FLAGS)) - 1
ALL = (1 << len(ROWS)) - 1
NEG = ALL ^ POS
INPUTS = [sum(1 << j for j, row in enumerate(ROWS) if row & (1 << i)) for i in range(2 * N)]


def prefix(dual):
    bank = {v: f"x{i}" for i, v in enumerate(INPUTS)}
    bank.update({0: "false", ALL: "true"})
    for c in range(1, N):
        members = sorted(LINES[c]) if dual else [N + l for l in range(N) if c in LINES[l]]
        for length in (2, 3, 4):
            for indices in combinations(members, length):
                val = reduce(or_, (INPUTS[i] for i in indices))
                bank[val] = "(" + "|".join(f"x{i}" for i in indices) + ")"
    shared = sum(1 << j for j, (p, l) in enumerate(FLAGS) if (l if dual else p) != 0)
    bank[shared] = "H"
    return bank


def accepting_nontrivial(v):
    return (v & POS) == POS and (v & NEG) not in (0, NEG)


def base_gates(bank):
    generated = {}
    for a, b in combinations(bank, 2):
        for symbol, v in (("&", a & b), ("|", a | b)):
            if v not in bank and v not in generated:
                generated[v] = f"({bank[a]}{symbol}{bank[b]})"
    return generated


def new_outputs(z, name, values, names):
    outputs = {}
    for v in values:
        for op, w in (("&", v & z), ("|", v | z)):
            if accepting_nontrivial(w) and w not in outputs:
                outputs[w] = f"({name}{op}{names[v]})"
    return outputs


def valid_pair(a, b):
    return accepting_nontrivial(a) and accepting_nontrivial(b) and (a & b & NEG) == 0


def search(dual):
    bank = prefix(dual)
    first = base_gates(bank)
    base_out = {v: s for v, s in bank.items() if accepting_nontrivial(v)}
    assert not base_out
    first_out = {v: s for v, s in first.items() if accepting_nontrivial(v)}
    # First gate supplies one of the outputs. The other can use two more gates.
    for a, sa in first_out.items():
        ext = bank | {a: sa}
        intermediate = first | base_gates(ext)
        for z, sz in intermediate.items():
            if valid_pair(a, z):
                return sa, sz
            for b, sb in new_outputs(z, sz, ext, ext).items():
                if valid_pair(a, b):
                    return sa, sb
    # Otherwise gates two and three must produce incomparable outputs.
    # A gate directly reading the other output would be comparable to it.
    for z, sz in first.items():
        possible = first_out | new_outputs(z, sz, bank, bank)
        for a, b in combinations(possible, 2):
            if valid_pair(a, b):
                return possible[a], possible[b]
    print(f"{'line' if dual else 'point'} stars: {len(bank)} free signatures, "
          f"{len(first)} distinct new first gates, {len(first_out)} eligible first outputs. No pair.")
    return None


if __name__ == "__main__":
    assert (len(FLAGS), len(QUADS)) == (52, 234)
    for dual in (False, True):
        witness = search(dual)
        if witness:
            print("Candidate in relaxed prefix model:", witness)
