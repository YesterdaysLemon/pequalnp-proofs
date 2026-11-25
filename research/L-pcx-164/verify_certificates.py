"""Replay both PHP(5,4) proofs with Python's ordinary sets of signed literals."""
from itertools import combinations
from pathlib import Path
import json


def replay(path):
    variables = range(1, 21)
    axioms = {frozenset(range(4*p+1, 4*p+5)) for p in range(5)}
    axioms.update(frozenset((-4*p-h-1, -4*q-h-1))
                  for p, q in combinations(range(5), 2) for h in range(4))
    clauses = []
    sources = []
    uses = []
    for j, ((p, n), why) in enumerate(json.loads(path.read_text())):
        assert 0 <= p < 1 << 20 and 0 <= n < 1 << 20 and not p & n
        clause = {v for v in variables if p & (1 << (v-1))}
        clause.update(-v for v in variables if n & (1 << (v-1)))
        if why is None:
            assert clause in axioms
            sources.append(frozenset(clause))
        else:
            left, right, pivot = why
            assert 0 <= left < j and 0 <= right < j and pivot in variables
            assert pivot in clauses[left] and -pivot in clauses[right]
            assert clause == (clauses[left] - {pivot}) | (clauses[right] - {-pivot})
            uses[left] += 1
            uses[right] += 1
        clauses.append(clause)
        uses.append(0)
    assert clauses and not clauses[-1]
    assert all(u >= 1 for u in uses[:-1]) and uses[-1] == 0
    assert set(sources) == axioms
    return len(clauses)-len(sources), len(sources), max(uses)


if __name__ == "__main__":
    root = Path(__file__).resolve().parent
    assert replay(root / "tree-certificate.json") == (188, 189, 1)
    hall_inferences, hall_axioms, _ = replay(root / "hall-certificate.json")
    assert (hall_inferences, hall_axioms) == (112, 45)
    print("Tree: 188 inferences, 189 axiom occurrences, 45 distinct axioms.")
    print("DAG: 112 inferences, 45 axiom occurrences, 45 distinct axioms.")
