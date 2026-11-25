"""Build small exact-synthesis inputs with the minimal-counterexample deletion limits."""
from pathlib import Path
from itertools import combinations
import sys,json
from minor_search import matching
from four_cover import graph_rows,neighbors


def first_gates(n,edges):
    adj=neighbors(n,edges)
    order=sorted(range(n),key=lambda i:(sum(len(k)==len(adj[i]) for k in adj),-len(adj[i]),i))
    pairs=list(combinations(range(n),2))
    reps=set(pairs)
    def visit(at,g,used):
        if at==n:
            for a,b in tuple(reps):
                if tuple(sorted((g[a],g[b])))<(a,b):
                    reps.remove((a,b))
            return
        x=order[at]
        for i in range(n):
            if used>>i&1 or len(adj[i])!=len(adj[x]):
                continue
            if any((p in adj[x])!=(g[p] in adj[i]) for p in order[:at]):
                continue
            g[x]=i
            visit(at+1,g,used|(1<<i))
    visit(0,[-1]*n,0)
    return reps


def write(directory):
    for c in json.loads((directory/"cores.json").read_text()):
        n=c["vertices"]
        edges=[tuple(e) for e in c["edges"]]
        k=len(edges)+matching(edges)-2
        pos,neg=graph_rows(n,edges)
        allowances=[]
        for v in range(n):
            rest=[e for e in edges if v not in e]
            allowances.append(k+1 if not rest else k-(len(rest)+matching(rest)-1))
        reps=first_gates(n,edges)
        assert len(pos)+len(neg)<=64
        fields=[[n,k,len(pos),len(neg),len(reps)],pos,neg,allowances]
        fields.extend(sorted(reps))
        (directory/(c["name"]+".debt")).write_text("".join(" ".join(map(str,r))+"\n" for r in fields))


if __name__=="__main__":
    write(Path(sys.argv[1]))
