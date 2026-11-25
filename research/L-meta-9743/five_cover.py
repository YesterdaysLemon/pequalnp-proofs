"""Unlabelled matching-five cores, using a distinguished minimum vertex cover."""
from collections import Counter
from functools import cache
from itertools import combinations, permutations, product
from pathlib import Path
import json
import sys
from four_cover import subsets, neighbors, square_free, full_matching, graph, graph_rows, forests


def canonical_graph(n, es):
    adj=neighbors(n,es)
    def visit(colors):
        while True:
            sig=[(colors[i],tuple(sorted(colors[j] for j in ns))) for i,ns in enumerate(adj)]
            ids={s:c for c,s in enumerate(sorted(set(sig)))}
            refined=tuple(ids[s] for s in sig)
            if len(set(colors))==len(ids):
                colors=refined
                break
            colors=refined
        blocks=[[i for i in range(n) if colors[i]==c] for c in range(len(set(colors)))]
        if all(len(b)==1 for b in blocks):
            return tuple(sorted(tuple(sorted((colors[a],colors[b]))) for a,b in es))
        chosen=min((b for b in blocks if len(b)>1),key=lambda b:(len(b),colors[b[0]]))
        out=[]
        for v in chosen:
            marked=list(colors)
            marked[v]=max(colors)+1
            out.append(visit(tuple(marked)))
        return min(out)
    return visit(tuple(map(len,adj)))


def line_pack(k,allowed):
    pairs={s:sum(1<<j for j,(u,v) in enumerate(combinations(range(k),2))
                 if s>>u&1 and s>>v&1) for s in allowed}
    def visit(start,used,chosen):
        yield chosen
        for j in range(start,len(allowed)):
            s=allowed[j]
            if not used & pairs[s]:
                yield from visit(j+1,used|pairs[s],chosen+(s,))
    return visit(0,0,())


def types(k):
    mapped=[]
    for p in permutations(range(k)):
        maps=[sum(1<<p[v] for v in range(k) if s>>v&1) for s in range(1<<k)]
        mapped.append((p,maps))
    def image(inside,shared,p,maps):
        return (tuple(sorted(tuple(sorted((p[a],p[b]))) for a,b in inside)),
                tuple(sorted(maps[s] for s in shared)))
    seen=set()
    for left in range(k//2+1):
        side=(1<<left)-1
        allowed=[s for s in range(1<<k) if s.bit_count()>=2 and (not s&side or s&side==s)]
        for shared in line_pack(k,allowed):
            for inside in subsets(list(product(range(left),range(left,k)))):
                key=(inside,shared)
                if key in seen:
                    continue
                seen.update(image(inside,shared,p,maps) for p,maps in mapped)
                if square_free(neighbors(k+len(shared),graph(k,inside,shared))):
                    yield inside,shared


def run(out,k=5):
    out.mkdir(exist_ok=True)
    cases={}
    for inside,shared in types(k):
        feasible=[s for s in sorted(subsets(tuple(range(k))),key=lambda s:(len(s),s))
                  if full_matching(k,shared+tuple(1<<i for i in s))]
        found=set()
        for av in range(1<<k):
            chosen=next((s for s in feasible if all(av>>i&1 for i in s)),None)
            if chosen is None or chosen in found:
                continue
            found.add(chosen)
            cs=shared+tuple(1<<i for i in chosen)
            n=k+len(cs)
            e=canonical_graph(n,graph(k,inside,cs))
            cases.setdefault(e,dict(k=k,vertices=n,edges=e,example=[inside,cs],forest=forests(n,e)))
    manifest=[]
    for i,(e,c) in enumerate(sorted(cases.items(),key=lambda t:(len(t[0]),t[0]))):
        name=f"h{i:03}"
        bound=len(e)+k-1
        manifest.append(dict(name=name,bound=bound,**c))
    (out/"cores.json").write_text(json.dumps(manifest,separators=(",",":"))+"\n")
    print("cases",len(manifest),"by edges",sorted(Counter(len(e) for e in cases).items()),flush=True)
    print("maximum inputs",max(c["vertices"] for c in manifest),flush=True)


if __name__=="__main__":
    run(Path(sys.argv[1]),int(sys.argv[2]) if len(sys.argv)>2 else 5)
