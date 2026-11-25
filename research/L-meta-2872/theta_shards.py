"""Minimum monotone circuits for the bipartite theta(3,3,3) graph.

The first gate is fixed up to graph symmetry. Only the remaining independent
gates are sorted. A satisfying circuit is checked on the full truth table.
The irredundancy checks are complete for minimum-size circuits.
"""
from argparse import ArgumentParser
from itertools import combinations, permutations
from pysat.formula import IDPool
from pysat.solvers import Solver


EDGES = frozenset([(0,4+i) for i in (1,2,3)]+[(i,4+i) for i in (1,2,3)]+[(i,4) for i in (1,2,3)])
POS = tuple((1<<a)|(1<<b) for a,b in sorted(EDGES))


def collision(mask):
    return any(mask&e == e for e in POS)


NEG = tuple(m for m in range(256) if not collision(m) and
            all(collision(m|1<<v) for v in range(8) if not m>>v&1))


def symmetries():
    sym = []
    for arm in permutations((1,2,3)):
        p = (0,)+arm+(4,)+tuple(x+4 for x in arm)
        sym.extend((p,tuple((x+4)%8 for x in p)))
    assert all({tuple(sorted((p[a],p[b]))) for a,b in EDGES} == EDGES for p in sym)
    return sym


def initial_gates():
    sym = symmetries()
    unseen = {(op,a,b) for a,b in combinations(range(8),2) for op in (0,1) if op==0 or (a,b) in EDGES}
    gates = []
    while unseen:
        op,a,b = min(unseen)
        gates.append((op,a,b))
        unseen.difference_update((op,min(p[a],p[b]),max(p[a],p[b])) for p in sym)
    return gates


def encode(s):
    pool = IDPool()
    cnf, ops, srcs, vals = [], [], [], []
    rows = POS+NEG
    for gate in range(s):
        width = 8+gate
        op = pool.id(("and",gate))
        ops.append(op)
        picks = [[pool.id(("pick",gate,side,i)) for i in range(width)] for side in (0,1)]
        srcs.append(picks)
        for p in picks:
            cnf.append(p)
            cnf.extend([-a,-b] for a,b in combinations(p,2))
        for a in range(width):
            for b in range(a+1):
                cnf.append([-picks[0][a],-picks[1][b]])
        witnesses = [[[],[]],[[],[]]]
        out = []
        for r,row in enumerate(rows):
            inputs = [pool.id(("read",gate,side,r)) for side in (0,1)]
            for side,h in enumerate(inputs):
                for i,p in enumerate(picks[side]):
                    if i<8:
                        cnf.append([-p,h if row>>i&1 else -h])
                    else:
                        val = vals[i-8][r]
                        cnf.extend(([-p,-h,val],[-p,h,-val]))
            a,b = inputs
            v = pool.id(("value",gate,r))
            out.append(v)
            cnf.extend(([-op,-v,a],[-op,-v,b],[-op,v,-a,-b],[op,v,-a],[op,v,-b],[op,-v,a,b]))
            for side in (0,1):
                w = pool.id(("diff",gate,side,r))
                cnf.extend(([-w,inputs[side]],[-w,-inputs[1-side]]))
                witnesses[int(r>=len(POS))][side].append(w)
            if gate==s-1:
                cnf.append([v if r<len(POS) else -v])
        vals.append(out)
        # OR must improve on both inputs on some positive rows. AND must
        # improve on both on some negative rows. Otherwise bypass the gate.
        for side in (0,1):
            cnf.append([op]+witnesses[0][side])
            cnf.append([-op]+witnesses[1][side])
        cnf.append(out[:len(POS)])
        cnf.append([-v for v in out[len(POS):]])
        if gate>=2:
            prev = srcs[gate-1]
            skip = [picks[1][width-1]]
            for a in range(width-1):
                for b in range(a):
                    cnf.append(skip+[-prev[0][a],-picks[0][b]])
                for b in range(a+1,width-1):
                    for d in range(a+1,b):
                        cnf.append(skip+[-prev[0][a],-picks[0][a],-prev[1][b],-picks[1][d]])
                    cnf.append(skip+[-prev[0][a],-picks[0][a],-prev[1][b],-picks[1][b],
                                     -ops[gate-1],op])
    for i in range(8):
        cnf.append([p[side][i] for p in srcs for side in (0,1)])
    for i in range(s-1):
        cnf.append([p[side][8+i] for p in srcs[i+1:] for side in (0,1)])
    return cnf,ops,srcs


def positive_control():
    raw = []
    def add(op,a,b):
        raw.append((op,a,b))
        return 7+len(raw)
    def disj(values):
        out,*rest = values
        for item in rest:
            out = add(0,out,item)
        return out
    stars = []
    for p in range(4):
        ns = sorted(l for a,l in EDGES if a==p)
        stars.append(add(1,p,disj(ns)))
    disj(stars)
    assert len(raw)==12
    image = next(perm for perm in symmetries()
                 if (raw[0][0],*sorted((perm[raw[0][1]],perm[raw[0][2]]))) in initial_gates())
    wires = dict(enumerate(image))
    gates = []
    while len(gates)<len(raw):
        ready = [(min(wires[a],wires[b]),max(wires[a],wires[b]),op,i)
                 for i,(op,a,b) in enumerate(raw) if 8+i not in wires and a in wires and b in wires
                 and (gates or i==0)]
        a,b,op,i = min(ready)
        wires[8+i] = 8+len(gates)
        gates.append((op,a,b))
    cnf,ops,srcs = encode(len(gates))
    fixed = []
    for (op,a,b),o,ss in zip(gates,ops,srcs):
        fixed.extend((o if op else -o,ss[0][a],ss[1][b]))
    with Solver(name="cadical195",bootstrap_with=cnf) as solver:
        assert solver.solve(assumptions=fixed)
    for m in range(256):
        vals=[bool(m>>i&1) for i in range(8)]
        for op,a,b in gates:
            vals.append(vals[a] and vals[b] if op else vals[a] or vals[b])
        assert vals[-1] == collision(m)
    print("12-gate control satisfies the CNF and all 256 truth-table rows",flush=True)


def search(s,budget):
    cnf,ops,srcs = encode(s)
    for kind,a,b in initial_gates():
        fixed = [ops[0] if kind else -ops[0],srcs[0][0][a],srcs[0][1][b]]
        with Solver(name="cadical195",bootstrap_with=cnf) as solver:
            solver.conf_budget(budget)
            result = solver.solve_limited(assumptions=fixed)
            print(s,("OR","AND")[kind],a,b,result,solver.accum_stats()["conflicts"],flush=True)
            if result is not True:
                continue
            model = set(solver.get_model())
        gates = [(op in model,*(next(i for i,p in enumerate(side) if p in model) for side in picks))
                 for op,picks in zip(ops,srcs)]
        for m in range(256):
            wires = [bool(m>>i&1) for i in range(8)]
            for use_and,i,j in gates:
                wires.append(wires[i] and wires[j] if use_and else wires[i] or wires[j])
            assert wires[-1] == collision(m)
        print("FULL TRUTH TABLE PASSED",gates,flush=True)
        return True
    return False


if __name__ == "__main__":
    p = ArgumentParser(description=__doc__)
    p.add_argument("size",type=int,nargs="?")
    p.add_argument("--conflicts",type=int,default=200000)
    a=p.parse_args()
    assert len(POS)==len(NEG)==9
    positive_control()
    if a.size is not None:
        search(a.size,a.conflicts)
