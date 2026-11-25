"""Probes for arbitrary zero/one restrictions with a known smaller edge-function cost."""
from itertools import combinations,product
from pathlib import Path
import json,sys
from four_cover import graph_rows
from minor_search import matching
from deletion_data import first_gates


def write(out,depth,names):
    for c in json.loads((out/"cores.json").read_text()):
        if names and c["name"] not in names: continue
        n=c["vertices"];es=tuple(map(tuple,c["edges"]));full=(1<<n)-1;budget=c["bound"]-1
        adjacency=[sum(1<<(b if a==v else a) for a,b in es if v in (a,b)) for v in range(n)]
        candidates=[]
        for count in range(1,depth+1):
            for coords in combinations(range(n),count):
                for values in product((0,1),repeat=count):
                    yes=sum(bit<<v for v,bit in zip(coords,values))
                    no=sum((1-bit)<<v for v,bit in zip(coords,values))
                    if any(yes&(1<<a) and yes&(1<<b) for a,b in es):continue
                    literals=0
                    for v in coords:
                        if yes&(1<<v):literals|=adjacency[v]
                    literals&=full^no
                    rest=full&~(yes|no|literals)
                    residual=tuple((a,b) for a,b in es if rest&(1<<a) and rest&(1<<b))
                    if not literals and not residual:continue
                    lower=literals.bit_count()+len(residual)+matching(residual)-1
                    slack=budget-lower-count
                    if slack>15:continue
                    candidates.append((slack, count,yes,no))
        candidates.sort()
        # Keep all one-coordinate restrictions affordable under the four-bit bound.
        required=[c for c in candidates if c[1]==1]
        probes=required+[c for c in candidates if c[1]>1][:64-len(required)]
        pos,neg=graph_rows(n,es)
        pairs=sorted(first_gates(n,es))
        fields=[[n,budget,len(pos),len(neg),len(pairs),len(probes)],pos,neg]
        fields.extend(sorted(pairs))
        fields.extend([[slack,yes,no] for slack,_,yes,no in probes])
        (out/(c["name"]+".multi")).write_text("".join(" ".join(map(str,r))+"\n" for r in fields))


if __name__=="__main__":
    write(Path(sys.argv[1]),int(sys.argv[2]),set(sys.argv[3:]))
