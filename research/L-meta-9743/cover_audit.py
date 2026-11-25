"""Check the core catalogue by enumerating all labelled pair assignments."""
from collections import defaultdict
from itertools import combinations, permutations
from pathlib import Path
import json,sys


def bits(x):
    while x:
        s=x&-x
        yield s
        x-=s


def covered_types(cases,k):
    have=defaultdict(set)
    for c in cases:
        if c["k"]!=k:continue
        n,es=c["vertices"],c["edges"]
        for cover in combinations(range(n),k):
            S=set(cover)
            if any(a not in S and b not in S for a,b in es):continue
            for order in permutations(cover):
                idx={v:i for i,v in enumerate(order)}
                inside=[];outside={}
                for a,b in es:
                    if a in S and b in S:
                        inside.append(tuple(sorted((idx[a],idx[b]))))
                    else:
                        i,q=(a,b) if a in S else (b,a)
                        outside[q]=outside.get(q,0)|(1<<idx[i])
                cols=list(outside.values())
                private=[q for q in cols if q.bit_count()==1]
                if len(set(private))!=len(private):continue
                shape=tuple(sorted(inside)),tuple(sorted(q for q in cols if q.bit_count()>1))
                have[shape].add(sum(private))
    return have


def by_pairs(k,left):
    pairs=[(a,b) for a,b in combinations(range(k),2) if (a<left)==(b<left)]
    side=(1<<left)-1
    possible=[]
    for s in range(1<<k):
        if s.bit_count()>=2 and (not s&side or s&side==s):
            used=sum(1<<i for i,(a,b) in enumerate(pairs) if s>>a&1 and s>>b&1)
            possible.append((s,used))
    def visit(remaining,columns):
        if not remaining:
            yield tuple(sorted(columns))
            return
        first=remaining&-remaining
        yield from visit(remaining^first,columns)
        for col,used in possible:
            if used&first and used&remaining==used:
                yield from visit(remaining^used,columns+(col,))
    yield from visit((1<<len(pairs))-1,())


def audit(cases,k):
    recorded=covered_types(cases,k)
    full=(1<<k)-1
    templates=valid=0
    for left in range(k//2+1):
        pairs=[(a,b) for a in range(left) for b in range(left,k)]
        for cs in by_pairs(k,left):
            reachable={0}
            for c in cs:
                reachable|={old|b for old in tuple(reachable) for b in bits(c&~old)}
            for m in range(1<<len(pairs)):
                inside=tuple(p for j,p in enumerate(pairs) if m>>j&1)
                # An outside shared neighbour and a cover vertex may close a square.
                adj=[0]*k
                for a,b in inside:adj[a]|=1<<b;adj[b]|=1<<a
                if any((x&y).bit_count()>1 for x,y in combinations(adj,2)):continue
                if any((a&s).bit_count()>1 for a in adj for s in cs):continue
                templates+=1
                subsets=recorded[inside,cs]
                for av in range(1<<k):
                    if any(full^r==(full^r)&av for r in reachable):
                        assert any((av&h)==h for h in subsets),(k,left,inside,cs,av)
                        valid+=1
    print("matching",k,"labelled shared-neighborhood templates",templates,
          "saturated private-neighborhood choices",valid,flush=True)


if __name__=="__main__":
    cases=json.loads(Path(sys.argv[1]).read_text())
    for k in sorted({c["k"] for c in cases}):
        audit(cases,k)
