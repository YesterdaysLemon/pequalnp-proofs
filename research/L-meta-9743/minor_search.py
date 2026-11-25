"""An independent monotone search using gate losses under vertex deletion."""
from functools import cache
from itertools import combinations
from pathlib import Path
import json
import sys


class Limit(Exception):
    pass


def matching(edges):
    @cache
    def best(vertex, remaining):
        if vertex<0:
            return 0
        if not (remaining>>vertex)&1:
            return best(vertex-1,remaining)
        remaining^=1<<vertex
        found=best(vertex-1,remaining)
        for x,y in edges:
            other=y if x==vertex else x if y==vertex else vertex
            if remaining>>other&1:
                found=max(found,1+best(vertex-1,remaining^(1<<other)))
        return found
    mask=sum(1<<i for i in {v for e in edges for v in e})
    return best(mask.bit_length()-1,mask)


def check(case, cap):
    n=case["vertices"]
    edges=tuple(tuple(e) for e in case["edges"])
    p=[(1<<a)|(1<<b) for a,b in edges]
    neighbors=[sum(1<<(b if i==a else a) for a,b in edges if i in (a,b)) for i in range(n)]
    q=[x for x in range(1<<n) if not any((x & e)==e for e in p) and
       all((x>>v)&1 or (x & neighbors[v]) for v in range(n))]
    positives=(1<<len(p))-1
    negatives=((1<<len(q))-1)<<len(p)
    universe=positives|negatives
    def signature(v):
        return sum(((row>>v)&1)<<i for i,row in enumerate(p+q))
    start=tuple(sorted((signature(v),1<<v) for v in range(n)))
    k=len(edges)+matching(edges)-2
    limits=[]
    for v in range(n):
        minor=tuple(e for e in edges if v not in e)
        # In a counterexample minimal in the number of edges, every nonempty minor
        # here obeys its edge-plus-matching bound. An empty minor imposes no limit.
        limits.append(k-(len(minor)+matching(minor)-1) if minor else k+1)
    visits=0
    checked=set()
    def solve(bank, budget, debt):
        nonlocal visits
        visits+=1
        if visits>cap:
            raise Limit
        if any(w==positives for w,m in bank):
            return True
        if len(bank)>budget+1 or not budget:
            return False
        key=(bank,budget,debt)
        if key in checked:
            return False
        for v,l in enumerate(debt):
            if l<sum((m>>v)&1 for _,m in bank):
                return False
        for j in range(len(q)):
            separated=0
            for w,_ in bank:
                if not w&(1<<(len(p)+j)):
                    separated|=w
            if separated&positives!=positives:
                return False
        for i,j in combinations(range(len(bank)),2):
            a,am=bank[i];b,bm=bank[j]
            consume=am|bm
            nd=tuple(l-((consume>>v)&1) for v,l in enumerate(debt))
            if min(nd)<0:
                continue
            for z,zm in ((a&b,am|bm),(a|b,am&bm)):
                if z & positives == 0 or z & negatives == negatives:
                    continue
                if any(z & ~w & positives == 0 and w & ~z & negatives == 0 for w,m in bank):
                    continue
                others=tuple(w for c,w in enumerate(bank) if c!=i and c!=j)
                for keep in ((),(bank[i],),(bank[j],),(bank[i],bank[j])):
                    if len(others)+len(keep)+1>budget:
                        continue
                    nxt=tuple(sorted(others+keep+((z&universe,zm),)))
                    if solve(nxt,budget-1,nd):
                        return True
        if len(checked)>90000:
            checked.clear()
        checked.add(key)
        return False
    try:
        result="SAT" if solve(start,k,tuple(limits)) else "UNSAT"
    except Limit:
        result="UNKNOWN"
    return result,visits


if __name__=="__main__":
    cases=json.loads(Path(sys.argv[1]).read_text())
    selected=set(sys.argv[3:])
    for case in cases:
        if selected and case["name"] not in selected:
            continue
        r,visits=check(case,int(sys.argv[2]))
        print(case["name"],r,visits,flush=True)
