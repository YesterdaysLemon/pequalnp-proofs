"""Share literal edge products across dirty gates of an exact monotone circuit."""

from collections import deque
from dataclasses import dataclass
from itertools import product


@dataclass(frozen=True)
class Gate:
    op: str
    inputs: tuple


@dataclass(frozen=True)
class Circuit:
    gates: tuple
    output: int


def wire_masks(circuit, initial, universe):
    bank = list(initial)
    for gate in circuit.gates:
        assert gate.op in ("and", "or") and len(gate.inputs) <= 2
        assert all(0 <= i < len(bank) for i in gate.inputs)
        value = universe if gate.op == "and" else 0
        for i in gate.inputs:
            value = value & bank[i] if gate.op == "and" else value | bank[i]
        bank.append(value)
    return bank


def inputs_for_rows(n, rows):
    return [sum(((row >> v) & 1) << j for j, row in enumerate(rows)) for v in range(2*n)]


def cross_rows(n):
    return [(1 << p) | (1 << (n+l)) for p, l in product(range(n), repeat=2)]


class Builder:
    """None denotes false. Gates only read real wires, and a missing output reads false."""

    def __init__(self, n):
        self.arity = 2*n
        self.gates = []
        self.memo = {}

    def add(self, op, args):
        if op == "and" and None in args:
            return None
        args = tuple(sorted({w for w in args if w is not None}))
        if op == "or" and not args:
            return None
        if len(args) == 1:
            return args[0]
        assert len(args) <= 2
        gate = Gate(op, args)
        if gate not in self.memo:
            self.memo[gate] = self.arity + len(self.gates)
            self.gates.append(gate)
        return self.memo[gate]

    def union(self, wires):
        answer = None
        for w in wires:
            answer = self.add("or", (answer, w))
        return answer

    def finish(self, output):
        live = set()
        todo = [] if output is None else [output]
        while todo:
            w = todo.pop()
            if w < self.arity or w in live:
                continue
            live.add(w)
            todo.extend(self.gates[w-self.arity].inputs)
        remap = dict(enumerate(range(self.arity)))
        gates = []
        for j, g in enumerate(self.gates, self.arity):
            if j in live:
                remap[j] = self.arity + len(gates)
                gates.append(Gate(g.op, tuple(remap[i] for i in g.inputs)))
        out = self.arity + len(gates) if output is None else remap[output]
        return Circuit(tuple(gates), out)


def favorable_groups(groups, required):
    """Maximum-weight closure. A selected signature pays once for each distinct flag."""
    signatures = list(groups)
    flags = sorted({bit for sig in signatures for bit in range(sig.bit_length()) if (sig >> bit) & 1})
    source, sink = 0, 1
    sig_node = {sig: j for j, sig in enumerate(signatures, 2)}
    flag_node = {bit: j for j, bit in enumerate(flags, 2+len(signatures))}
    capacity = [{} for _ in range(2+len(signatures)+len(flags))]

    def arc(a, b, c):
        capacity[a][b] = capacity[a].get(b, 0) + c
        capacity[b].setdefault(a, 0)

    weights = {sig: len(js)-max(0, sig.bit_count()-1) for sig, js in groups.items()}
    infinite = 1 + sum(map(abs, weights.values())) + len(flags)
    for sig, node in sig_node.items():
        weight = weights[sig]
        if weight > 0:
            arc(source, node, weight)
        elif weight < 0:
            arc(node, sink, -weight)
        if sig in required:
            arc(source, node, infinite)
        for flag in flags:
            if (sig >> flag) & 1:
                arc(node, flag_node[flag], infinite)
    for node in flag_node.values():
        arc(node, sink, 1)

    # Edmonds-Karp. The reachable side of the final residual cut gives the batch.
    while True:
        parent = {source: None}
        queue = deque([source])
        while queue and sink not in parent:
            a = queue.popleft()
            for b, c in capacity[a].items():
                if c > 0 and b not in parent:
                    parent[b] = a
                    queue.append(b)
        if sink not in parent:
            return {sig for sig, node in sig_node.items() if node in parent}
        path = []
        b = sink
        while b != source:
            a = parent[b]
            path.append((a, b))
            b = a
        amount = min(capacity[a][b] for a, b in path)
        for a, b in path:
            capacity[a][b] -= amount
            capacity[b][a] += amount


def construction_cost(size, groups, selected):
    used = 0
    for sig in selected:
        used |= sig
    return (size - sum(len(groups[sig]) for sig in selected) + used.bit_count() +
            sum(max(0, sig.bit_count()-1) for sig in selected))


def clean(n, edges, circuit, verify_optimum=False):
    """Return a clean circuit, its optimal batch bound, and the dirty-only bound."""
    rows = cross_rows(n)
    universe = (1 << len(rows)) - 1
    old = wire_masks(circuit, inputs_for_rows(n, rows), universe)
    groups = {}
    required = set()
    mandatory_gates = {}
    for j, gate in enumerate(circuit.gates):
        sig = old[2*n+j] & edges
        groups.setdefault(sig, []).append(j)
        if gate.op == "and" and old[2*n+j] & (universe ^ edges):
            required.add(sig)
            mandatory_gates.setdefault(sig, []).append(j)

    signatures = favorable_groups(groups, required)
    mandatory_bound = construction_cost(len(circuit.gates), mandatory_gates, required)
    bound = construction_cost(len(circuit.gates), groups, signatures)
    assert required <= signatures and bound <= mandatory_bound
    if verify_optimum:
        optional = sorted(set(groups)-required)
        assert bound == min(construction_cost(len(circuit.gates), groups, required |
            {sig for sig, take in zip(optional, bits) if take}) for bits in product((0, 1), repeat=len(optional)))
    rewritten = {j: sig for sig in signatures for j in groups[sig]}
    used = 0
    for sig in signatures:
        used |= sig

    b = Builder(n)
    products = {i: b.add("and", divmod_as_wires(n, i)) for i in range(n*n) if (used >> i) & 1}
    replacement = {sig: b.union(w for i, w in products.items() if (sig >> i) & 1)
                   for sig in sorted(signatures)}
    image = list(range(2*n))
    for j, gate in enumerate(circuit.gates):
        if j in rewritten:
            image.append(replacement[rewritten[j]])
        else:
            image.append(b.add(gate.op, tuple(image[i] for i in gate.inputs)))
    # A union of all genuine edge products is itself the requested function.
    if not edges:
        out = None
    elif edges in replacement:
        out = replacement[edges]
    else:
        out = image[circuit.output] if circuit.output < len(image) else None
    answer = b.finish(out)
    assert len(answer.gates) <= bound
    return answer, bound, mandatory_bound


def divmod_as_wires(n, edge):
    p, l = divmod(edge, n)
    return p, n+l


def target(n, edges, x):
    return any((edges >> i) & 1 and x & row == row for i, row in enumerate(cross_rows(n)))


def dual_circuit(n, edges, reverse=False):
    """An exact circuit from maximal independent sets, with singleton-off AND gates."""
    b = Builder(n)
    pts = b.union(range(n))
    lines = b.union(range(n, 2*n))
    out = b.add("and", (pts, lines))
    independent = {x for x in range(1 << (2*n)) if not target(n, edges, x)}
    maximal = sorted((x for x in independent if all(
        (x | (1 << v)) not in independent for v in range(2*n) if not (x >> v) & 1)),
        reverse=reverse)
    for x in maximal:
        clause = b.union(v for v in range(2*n) if not (x >> v) & 1)
        out = b.add("and", (out, clause))
    return b.finish(out)


def c4_free(n, edges):
    rows = [(edges >> (p*n)) & ((1 << n)-1) for p in range(n)]
    return all((a & b).bit_count() < 2 for i, a in enumerate(rows) for b in rows[:i])


def check(n, edges, circuit, must_be_clean):
    all_rows = range(1 << (2*n))
    full = (1 << len(all_rows)) - 1
    bank = wire_masks(circuit, inputs_for_rows(n, all_rows), full)
    output = bank[circuit.output] if circuit.output < len(bank) else 0
    assert output == sum(target(n, edges, x) << x for x in all_rows)
    reject = sum(1 << (1 << v) for v in range(2*n))
    if must_be_clean:
        reject |= sum(1 << x for i, x in enumerate(cross_rows(n)) if not (edges >> i) & 1)
    assert all(not bank[2*n+j] & reject for j, g in enumerate(circuit.gates) if g.op == "and")


def main():
    for n in (2, 3):
        graphs = trials = no_growth = paid = dirty_only_paid = 0
        largest_saving = 0
        for edges in range(1 << (n*n)):
            if not c4_free(n, edges):
                continue
            graphs += 1
            for reverse in (False, True):
                old = dual_circuit(n, edges, reverse)
                check(n, edges, old, False)
                new, bound, mandatory_bound = clean(n, edges, old, verify_optimum=True)
                check(n, edges, new, True)
                trials += 1
                paid += bound <= len(old.gates)
                dirty_only_paid += mandatory_bound <= len(old.gates)
                no_growth += len(new.gates) <= len(old.gates)
                largest_saving = max(largest_saving, len(old.gates)-len(new.gates))
        print(f"N={n}: {graphs} graphs, {trials} circuit trials, {dirty_only_paid} dirty-only "
              f"and {paid} optimized batches meet the bound, {no_growth} clean without growth, "
              f"largest saving {largest_saving}")


if __name__ == "__main__":
    main()
