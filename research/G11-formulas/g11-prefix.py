"""Classify possible single shared subformulas by their boundary evaluations."""
from argparse import ArgumentParser
from collections import Counter
from itertools import combinations
from functools import lru_cache
from importlib.util import module_from_spec,spec_from_file_location
from pathlib import Path
import json
import sys

base=Path(__file__).resolve().parent
spec=spec_from_file_location("kw",base/"graph-kw.py")
kw=module_from_spec(spec);sys.dont_write_bytecode=True;spec.loader.exec_module(kw)

def main():
    ap=ArgumentParser(description=__doc__);ap.add_argument("out",type=Path);ap.add_argument("--max",type=int,default=4)
    a=ap.parse_args()
    pc=[(1<<u)|(1<<v) for u,v in kw.edges];nc,_=kw.structure(kw.edges)
    allrows=(1<<len(pc))-1;allcols=(1<<len(nc))-1
    star=[sum(1<<j for j,c in enumerate(pc) if c>>v&1) for v in range(11)]
    present=[sum(1<<j for j,c in enumerate(nc) if c>>v&1) for v in range(11)]
    leaves=[x|y<<len(pc) for x,y in zip(star,present)]
    unions={0:(0,0)}
    for s in range(1,2048):
        bit=s&-s;v=bit.bit_length()-1;r,c=unions[s^bit]
        unions[s]=r|star[v],c|present[v]
    @lru_cache(maxsize=32768)
    def single(B):
        hidden=sum(1<<v for v,b in enumerate(present) if not B&b)
        return unions[hidden][0]
    def row_cost(A,B):
        return 0 if not B else 2*A.bit_count()-(A&single(B)).bit_count()
    def reason(w,t):
        A=w&allrows;B=allcols^(w>>len(pc))
        if not A or not B:return "empty"
        if row_cost(A,B)<=t+2:return "one or two labels per row"
        # Reassign the intersection with an OR rectangle to the chosen OR.
        # Handle the rest a single original edge at a time.
        for s in candidates[t]:
            r,c=unions[s]
            if s.bit_count()-1+row_cost(A&~r,B)+row_cost(A&r,B&c)<=t:return "reusable OR"
        return None
    layers=[set(leaves)];seen=set(leaves);summary=[];unresolved={}
    candidates=[sorted((s for s in range(1,2048) if s.bit_count()<=k+1),key=lambda s:(s.bit_count(),s)) for k in range(a.max+1)]
    for t in range(1,a.max+1):
        fresh=set()
        for k in range((t-1)//2+1):
            for u in layers[k]:
                for v in layers[t-1-k]:
                    fresh.add(u&v);fresh.add(u|v)
        fresh-=seen;seen|=fresh;layers.append(fresh)
        count=Counter()
        for w in sorted(fresh):
            mark=reason(w,t)
            count[mark or "unresolved"]+=1
            if mark is None:unresolved[f"{w:x}"]=t
        summary.append(dict(count))
        print("gates",t,"signatures",len(fresh),dict(count),flush=True)
        a.out.write_bytes(json.dumps({"statistics":summary,"unresolved":unresolved},separators=(",",":")).encode())

if __name__=="__main__":main()
