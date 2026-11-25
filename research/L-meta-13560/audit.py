from pathlib import Path
import re


source = Path(__file__).resolve().parent
target = 0xEEE8EAE0EEC8EAC0
gates = re.findall(r"^(\d+) = ([&|]) (\d+) (\d+)$",
                   (source / "monotone-witness.txt").read_text(), re.M)
assert len(gates) == 8
for row in range(64):
    wires = [row >> v & 1 for v in range(6)]
    for out, op, a, b in gates:
        assert int(out) == len(wires)
        x, y = wires[int(a)], wires[int(b)]
        wires.append(x & y if op == "&" else x | y)
    assert wires[-1] == (target >> row & 1)
print("Eight-gate witness verified on all 64 rows")

monotone = [0, 1]
for n in range(5):
    monotone = [a | b << (1 << n) for a in monotone for b in monotone if a & ~b == 0]
assert len(monotone) == 7581
for i, expected, count in [(5, 0xEEE8EAE0, 1107), (4, 0xEEE8EEC8, 1261)]:
    def insert_one(v):
        return v % (1 << i) + (1 << i) + (v >> i << (i + 1))
    cofactor = sum((target >> insert_one(v) & 1) << v for v in range(32))
    assert cofactor == expected
    found = sum(a != cofactor and a & ~cofactor == 0 for a in monotone)
    assert found == count
    print(f"Input {i} fixed to one, cofactor {cofactor:#x}, {found} essential monotone extensions")
