"""Classify graph edge functions up to relabeling and check each returned circuit on every row."""
from collections import Counter
from itertools import permutations
from pathlib import Path
import argparse
import json
import re
import subprocess


def pairs(n):
    return [(i,j) for j in range(1,n) for i in range(j)]


def representative_orbits(n):
    edges=pairs(n)
    at={edge:i for i,edge in enumerate(edges)}
    maps=[[at[tuple(sorted((p[i],p[j])))] for i,j in edges] for p in permutations(range(n))]
    seen=set()
    for graph in range(1,1<<len(edges)):
        if graph in seen:
            continue
        chosen=[i for i in range(len(edges)) if graph>>i&1]
        orbit={sum(1<<p[i] for i in chosen) for p in maps}
        seen.update(orbit)
        vertices=set(v for i in chosen for v in edges[i])
        if len(vertices)==n:
            yield graph,len(orbit),[edges[i] for i in chosen]


def run(binary,n,graph,edges,basis,cap):
    out=subprocess.check_output([str(binary),str(n),str(graph),basis,str(cap)],text=True)
    mask=(1<<n)-1
    found=int(re.search(rf"^lower {mask} (\d+)$",out,re.M)[1])
    record={"lower":found}
    last=[line for line in out.splitlines() if line.startswith(f"{mask} budget ")][-1]
    size,verdict,nodes,gates=re.fullmatch(r"\d+ budget (\d+) (\w+) visits (\d+)(?: gates (.*))?",last).groups()
    record.update(status=verdict,visits=int(nodes))
    if verdict=="SAT":
        ops=[tuple(map(int,token.split(","))) for token in gates.split()]
        assert len(ops)==int(size)==found
        for x in range(1<<n):
            w=[bool(x>>i&1) for i in range(n)]
            for op,a,b in ops:
                assert a<len(w) and b<len(w) and (0<=op<(2 if basis=="mono" else 5))
                left,right=w[a],w[b]
                w.append([left and right,left or right,left and not right,right and not left,left!=right][op])
            assert w[-1]==any((x>>a)&(x>>b)&1 for a,b in edges)
        record["gates"]=ops
    return record


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("binary",type=Path)
    p.add_argument("output",type=Path)
    p.add_argument("--size",type=int,default=5)
    p.add_argument("--cap",type=int,default=3000000)
    args=p.parse_args()
    result=[]
    for g,count,edges in representative_orbits(args.size):
        row={"mask":g,"multiplicity":count,"edges":edges}
        for basis in ("full","mono"):
            row[basis]=run(args.binary,args.size,g,edges,basis,args.cap)
        result.append(row)
        print(g,count,len(edges),row["full"]["status"],row["full"]["lower"],row["mono"]["status"],row["mono"]["lower"],flush=True)
    args.output.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print("class count",len(result),"labeled graphs",sum(r["multiplicity"] for r in result))
    print("full lower bounds by class",sorted(Counter(r["full"]["lower"] for r in result).items()))
