from argparse import ArgumentParser
from itertools import combinations
from pathlib import Path
import json
import os
import random
import runpy

def search(candidates,goal,seconds):
    from time import monotonic
    rng=random.Random(1894)
    best=[]
    deadline=monotonic()+seconds
    while monotonic()<deadline:
        selected=[]
        covered=0
        if best and rng.random()<0.78:
            keep=rng.randrange(max(0,len(best)-8),len(best)-2)
            selected=rng.sample(best,keep)
            for i in selected:covered|=candidates[i]
        while covered!=goal and (not best or len(selected)<len(best)-1):
            un=goal^covered
            scores=[(c&un).bit_count() for c in candidates]
            high=max(scores)
            penalty=rng.choice([0,0,0,1,1,2]) if un.bit_count()>15 else 0
            options=[i for i,x in enumerate(scores) if x>=max(1,high-penalty)]
            j=rng.choice(options);selected.append(j);covered|=candidates[j]
        if covered==goal and (not best or len(selected)<len(best)):
            best=selected
            print("found",len(best),"tests",flush=True)
    return best

def main():
    parser=ArgumentParser()
    parser.add_argument("output",type=Path);parser.add_argument("--seconds",type=int,default=12)
    a=parser.parse_args()
    z=runpy.run_path(str(Path(__file__).resolve().parent/"plane-dual.py"))
    edges,P,L,pc,*_=z["points_lines"](4)
    pairs=[(x,y) for x,y in combinations(range(42),2) if not(x<21<=y and (y-x)%21 in z['SETS'][4])]
    tests=[]
    for p,l in zip(P,L):
        if sorted([int(pc[p]),int(pc[l])]) not in ([6,6],[0,21],[1,16]):continue
        mask=int(p)|(int(l)<<21);tests.append([i for i in range(42) if mask>>i&1])
    sets=[sum(1<<i for i,(x,y) in enumerate(pairs) if x in T and y in T) for T in tests]
    best=search(sets,(1<<len(pairs))-1,a.seconds)
    out=[tests[i] for i in best]
    assert all(any(x in T and y in T for T in out) for x,y in pairs)
    assert all(all(not(p in T and l+21 in T) for p,l in edges) for T in out)
    a.output.write_bytes((json.dumps(out)+"\n").encode())

if __name__=="__main__":main()
