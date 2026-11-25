"""Print the Lean data declarations for one signed-circuit certificate."""
import argparse
from collections import deque
from itertools import combinations
import json
from pathlib import Path


def pack(width, values):
    """Use little-endian, fixed-width fields in a single natural number."""
    out = 0
    for index, value in enumerate(values):
        if not 0 <= value < 1 << width:
            raise ValueError(f"{value} exceeds {width}-bit field")
        out |= value << (width * index)
    return out


def lean_list(items):
    return "[" + ",".join(map(str, items)) + "]"


def row_swaps(variable_count):
    """Encode each coordinate permutation as transpositions of two bit positions."""
    size = 1 << variable_count
    identity = tuple(range(size))
    found = {identity: []}
    queue = deque([identity])
    swaps = []
    for i, j in combinations(range(variable_count), 2):
        low, high = 1 << i, 1 << j
        distance = high - low
        up = sum(1 << x for x in range(64) if x & low and not x & high)
        down = sum(1 << x for x in range(64) if x & high and not x & low)
        perm = [x + distance if up >> x & 1 else x - distance if down >> x & 1 else x
                for x in range(size)]
        swaps.append((perm, [distance, up, down]))
    while queue:
        parent = queue.popleft()
        for perm, code in swaps:
            child = tuple(parent[p] for p in perm)
            if child not in found:
                found[child] = code + found[parent]
                queue.append(child)
    return found


def encode_arc(tag, child, symmetry, bank_size):
    pair, choice = divmod(tag, 16)
    left, right = divmod(pair, 16)
    if not 0 <= left < right < bank_size:
        raise ValueError("invalid operand pair")
    ordinal = left * (2 * bank_size - left - 1) // 2 + right - left - 1
    short_tag = 1 + 16 * ordinal + choice
    if short_tag >= 1024 or child >= 2048 or symmetry >= 32:
        raise ValueError("arc exceeds its packed field")
    return symmetry << 21 | child << 10 | short_tag


def table(case, reasons):
    words = sorted({w for layer in case["layers"] for row in layer for w in row["bank"]})
    word_id = {w: i + 1 for i, w in enumerate(words)}
    codes = row_swaps(len(case["labels"]))
    syms = []
    for rowmap in case["rowmaps"]:
        inverse = tuple(rowmap.index(i) for i in range(len(rowmap)))
        syms.append("(" + lean_list(map(hex, codes[inverse])) + "," +
                    lean_list(map(hex, codes[tuple(rowmap)])) + ")")
    lines = [
        f"def y : W := {hex(case['y'])}",
        f"def base : List W := {lean_list(map(hex, case['initial']))}",
        f"def neg : List (Fin 64) := {lean_list(case['negative'])}",
        f"def dict : ℕ := {hex(pack(64, words))}",
        f"def masks : List W := {lean_list(map(hex, case['masks']))}",
        "def ds : Debts := " + lean_list(f"({hex(m)},{r})" for m, r in
                                       zip(case["masks"], case["layers"][-1][0]["need"])),
        "def syms : Array Sym := #" + lean_list(syms),
        f"def book : ℕ := {hex(pack(80, reasons['patterns']))}",
        "def ck (p c : Catalogue) (k start : ℕ) (hs : List Hint) : Bool :=\n"
        "  auditRows (checkEntry y neg dict masks syms book p k) c start hs",
    ]
    for k, layer in enumerate(case["layers"]):
        banks = [pack(10, [word_id[w] for w in row["bank"]]) for row in layer]
        debts = [pack(4, row["need"]) for row in layer]
        width = max((v.bit_length() for v in banks), default=1)
        lines.append(f"def c{k} : Catalogue := ({len(layer)},{width},"
                     f"{hex(pack(width, banks))},{hex(pack(32, debts))})")
        for start in range(0, len(layer), 24):
            rows = []
            for i in range(start, min(start + 24, len(layer))):
                record = layer[i]
                arcs = pack(26, (encode_arc(*arc, len(record["bank"])) for arc in record["arcs"]))
                groups = pack(11, reasons["groups"][k][i])
                rows.append(f"({hex(arcs) if arcs else '0'},{hex(groups) if groups else '0'})")
            lines.append(f"def r{k}_{start // 24} : List Hint := [" + ",\n  ".join(rows) + "]")
    return "\n\n".join(lines)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("case", choices=["clique", "universal", "six"])
    args = parser.parse_args()
    folder = Path(__file__).resolve().parent
    graph = json.loads((folder / f"seven-cert-{args.case}.json").read_bytes())
    reasons = json.loads((folder / f"seven-reasons-{args.case}.json").read_bytes())
    print(table(graph, reasons))
