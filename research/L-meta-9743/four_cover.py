"""Enumerate finite cores of all square-free bipartite graphs of matching size at most four."""
from collections import Counter, defaultdict
from itertools import combinations, permutations, product
from pathlib import Path
import json
import sys


def subsets(items):
    for size in range(len(items)+1):
        yield from combinations(items,size)


def full_matching(k, columns):
    def visit(remaining, picked):
        if not remaining:
            return True
        i=remaining[0]
        return any(j not in picked and col>>i&1 and visit(remaining[1:],picked|{j})
                   for j,col in enumerate(columns))
    return visit(list(range(k)),set())


def neighbors(n, edges):
    adj=[set() for _ in range(n)]
    for a,b in edges:
        adj[a].add(b)
        adj[b].add(a)
    return adj


def square_free(adj):
    return all(len(a&b)<=1 for a,b in combinations(adj,2))


def encode(n, edges):
    # Color refinement reduces the number of labelings needed for canonicalization.
    adj=neighbors(n,edges)
    colors=[len(ns) for ns in adj]
    while True:
        signatures=[(colors[i],tuple(sorted(colors[j] for j in adj[i]))) for i in range(n)]
        palette={s:c for c,s in enumerate(sorted(set(signatures)))}
        new=[palette[s] for s in signatures]
        if len(set(colors))==len(palette):
            colors=new
            break
        colors=new
    blocks=[[i for i,c in enumerate(colors) if c==color] for color in sorted(set(colors))]
    best=None
    for parts in product(*(permutations(b) for b in blocks)):
        order=sum(parts,())
        mapping={old:i for i,old in enumerate(order)}
        signature=tuple(sorted(tuple(sorted((mapping[a],mapping[b]))) for a,b in edges))
        if best is None or signature<best:
            best=signature
    return best


def forests(n,edges):
    parent=list(range(n))
    def root(x):
        while x!=parent[x]:
            x=parent[x]
        return x
    for a,b in edges:
        a,b=root(a),root(b)
        if a==b:
            return False
        parent[a]=b
    return True


def graph(k, internal, cols):
    return tuple(sorted(internal+tuple((i,k+j) for j,s in enumerate(cols) for i in range(k) if s>>i&1)))


def graph_rows(n,edges):
    positive=sorted((1<<a)|(1<<b) for a,b in edges)
    adj=[sum(1<<j for j in ns) for ns in neighbors(n,edges)]
    negative=[r for r in range(1<<n) if not any(r&e==e for e in positive) and
              all(r>>i&1 or r&ns for i,ns in enumerate(adj))]
    assert all(any(p&~q==1<<i for p in positive for q in negative) for i in range(n))
    return positive,negative


def point_types(k):
    for left in range(k//2+1):
        color=(1<<left)-1
        internal=list(product(range(left),range(left,k)))
        multiples=[s for s in range(1<<k) if s.bit_count()>=2 and (not s&color or s&color==s)]
        for inside in subsets(internal):
            for cols in subsets(multiples):
                if any((s&t).bit_count()>1 for s,t in combinations(cols,2)):
                    continue
                if square_free(neighbors(k+len(cols),graph(k,inside,cols))):
                    yield inside,cols


def run(out):
    out.mkdir(exist_ok=True)
    cases={}
    normalized={}
    for k in range(1,5):
        for inside,shared in point_types(k):
            matchable=[s for s in sorted(subsets(tuple(range(k))),key=lambda s:(len(s),s))
                       if full_matching(k,shared+tuple(1<<i for i in s))]
            for available in range(1<<k):
                kept=next((s for s in matchable if all(available>>i&1 for i in s)),None)
                if kept is None:
                    continue
                cols=shared+tuple(1<<i for i in kept)
                n=k+len(cols)
                labelled=graph(k,inside,cols)
                cache_key=(n,labelled)
                if cache_key not in normalized:
                    normalized[cache_key]=encode(n,labelled)
                signature=normalized[cache_key]
                if signature not in cases:
                    cases[signature]=dict(k=k,vertices=n,edges=signature,instances=0,
                                          example=[inside,cols],forest=forests(n,signature))
                c=cases[signature]
                assert c["k"]==k
                c["instances"]+=1
    manifest=[]
    for i,(e,c) in enumerate(sorted(cases.items(),key=lambda t:(t[1]["k"],len(t[0]),t[0]))):
        name=f"g{i:03}";n=c["vertices"];bound=len(e)+c["k"]-1
        pos,neg=graph_rows(n,e)
        (out/(name+".rows")).write_text(f"{n} {bound-1} {len(pos)} {len(neg)}\n"+
                                         " ".join(map(str,pos))+"\n"+" ".join(map(str,neg))+"\n")
        manifest.append(dict(name=name,bound=bound,**c))
    (out/"cores.json").write_text(json.dumps(manifest,indent=1)+"\n")
    print("cores by matching size and acyclicity",sorted(Counter((c["k"],c["forest"]) for c in manifest).items()))
    print("maximum inputs",max(c["vertices"] for c in manifest),"maximum edges",max(len(c["edges"]) for c in manifest))
    print("cyclic cores",[(c["name"],c["vertices"],len(c["edges"]),c["bound"]) for c in manifest if not c["forest"]])


if __name__=="__main__":
    run(Path(sys.argv[1]))
