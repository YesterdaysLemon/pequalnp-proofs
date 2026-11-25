"""Find and verify rectangle-partition lower bounds for finite projective planes."""
from argparse import ArgumentParser
from itertools import combinations
from pathlib import Path
import json
import numpy as np

SETS = {2:(0,1,3), 3:(0,1,3,9), 4:(0,5,7,17,20)}


def points_lines(q):
    v = q*q + q + 1
    full = (1 << v) - 1
    flags = [(p, l) for p in range(v) for l in range(v) if (l-p)%v in SETS[q]]
    ps = [sum(1 << l for a,l in flags if a==p) for p in range(v)]
    ls = [sum(1 << p for p,b in flags if b==l) for l in range(v)]
    def avoiding(neighbors):
        out = np.empty(1 << v, dtype=np.int32)
        out[0] = full
        for i, n in enumerate(neighbors):
            power = 1 << i
            out[power:power*2] = out[:power] & (full ^ n)
        return out
    indices = np.arange(1 << v, dtype=np.int32)
    lp, pl = avoiding(ps), avoiding(ls)
    P = indices[pl[lp] == indices]
    L = lp[P]
    pop = np.empty(1 << v, dtype=np.int8)
    pop[0] = 0
    for i in range(v):
        power = 1 << i
        pop[power:2*power] = 1 + pop[:power]
    return flags, P, L, pop, ps, ls


def instances(q):
    edges, P, L, pc, ps, ls = points_lines(q)
    szp, szl = pc[P].astype(np.int32), pc[L].astype(np.int32)
    features = []
    for p,l in edges:
        a = ((szp*2+(P>>p&1))*(q+2)+pc[L & ps[p]])
        b = ((szl*2+(L>>l&1))*(q+2)+pc[P & ls[l]])
        features.append(np.minimum(a,b)*512+np.maximum(a,b))
    keys, inv, counts = np.unique(np.array(features).ravel(), return_inverse=True, return_counts=True)
    ids = inv.astype(np.int32).reshape((len(edges),len(P)))
    return (edges, P, L, ps, ls, keys, ids, counts)


def solve(q, data):
    from scipy.optimize import linprog
    from scipy.sparse import coo_matrix
    edges, P, L, ps, ls, keys, ids, counts = data
    v, m = len(ps), len(keys)
    rows, cols, vals, rhs = [], [], [], []
    objective = (-counts).astype(float).tolist()
    label = [i for i,(p,l) in enumerate(edges) if p==0]
    absent = (P & 1) == 0
    def term(row, col, val):
        rows.append(row); cols.append(col); vals.append(val)
    for k in range(1, len(label)+1):
        options = ids[label[:k]][:,absent].T
        types, multiplicity = np.unique(np.sort(options,axis=1), axis=0, return_counts=True)
        r = len(rhs); rhs.append(1.)
        for group, mult in zip(types,multiplicity):
            col = len(objective); objective.append(0.)
            term(r, col, int(mult))
            req = len(rhs); rhs.append(0.)
            for i in group:term(req,int(i),1)
            term(req,col,-1)
    mat = coo_matrix((vals,(rows,cols)),shape=(len(rhs),len(objective))).tocsr()
    sol = linprog(objective, A_ub=mat, b_ub=rhs, bounds=[(-2.,2.)]*m+[(0,None)]*(len(objective)-m),
                  method="highs",options={"threads":1,"primal_feasibility_tolerance":1e-9})
    if not sol.success:raise ValueError(sol.message)
    print("features",m,"LP constraints",len(rhs),"optimum",-sol.fun,flush=True)
    return {int(k):int(w) for k,w in zip(keys,np.rint(sol.x[:m]*10**8).astype(np.int64)) if w}


def verify(q, data, weights):
    edges, P, L, ps, ls, keys, ids, counts = data
    w = np.array([weights.get(int(k),0) for k in keys],dtype=np.int64)
    bound = 0
    for side,masks in enumerate((P,L)):
        for v in range(len(ps)):
            rows = [i for i,e in enumerate(edges) if e[side]==v]
            subset = w[ids[rows][:,(masks>>v&1)==0]]
            for k in range(1,len(rows)+1):
                for group in combinations(range(len(rows)),k):
                    sums = np.sum(subset[list(group)],axis=0)
                    bound = max(bound,int(np.maximum(sums,0).sum()))
    total = int(w@counts.astype(np.int64))
    assert bound>0 and total>0
    leaves = (total+bound-1)//bound
    print("q",q,"edges",len(edges),"maximal negatives",len(P),"numerator",total,"denominator",bound,"leaves",leaves,"gates",leaves-1,flush=True)
    return dict(order=q, flags=len(edges), negative_inputs=len(P), total=total, max_rectangle=bound, leaves=leaves, gates=leaves-1)


if __name__=="__main__":
    parser=ArgumentParser(description=__doc__)
    parser.add_argument("q",type=int,choices=SETS);parser.add_argument("file",type=Path);parser.add_argument("--check", action="store_true")
    args=parser.parse_args(); data=instances(args.q)
    if args.check:
        rec=json.loads(args.file.read_bytes());weights={int(k):v for k,v in rec["weights"].items()}
        assert verify(args.q,data,weights)==rec["result"]
    else:
        weights=solve(args.q,data); result=verify(args.q,data,weights)
        args.file.write_bytes((json.dumps(dict(result=result,weights=weights),indent=2)+"\n").encode())
