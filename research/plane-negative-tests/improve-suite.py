"""Repair negative test families by coloring the nonadjacent pairs they leave uncovered."""
from argparse import ArgumentParser
from itertools import combinations
from pathlib import Path
from pysat.solvers import Solver
import json, random, runpy, time

def indices(mask):
    while mask:
        b=mask&-mask
        yield b.bit_length()-1
        mask^=b

def coloring(U,neighbors,k,cap,rng):
    if U==0:return []
    options=U;clique=[]
    while options:
        v=max(indices(options),key=lambda a: (neighbors[a]&options).bit_count())
        clique.append(v);options&=neighbors[v]
    if len(clique)>k:return None
    labels=list(indices(U)); rng.shuffle(labels); pos={v:i for i,v in enumerate(labels)}
    var=lambda v,c: pos[v]*k+c+1
    cs=[[var(v,c) for c in range(k)] for v in labels]
    for i,v in enumerate(clique):cs.append([var(v,i)])
    for v in labels:
        for j in indices(neighbors[v]&U&((1<<v)-1)):
            cs.extend([-var(v,c),-var(j,c)] for c in range(k))
    with Solver(name='cadical195',bootstrap_with=cs) as sol:
        sol.conf_budget(cap);out=sol.solve_limited()
        if not out:return None
        model=set(sol.get_model())
    ans=[[] for _ in range(k)]
    for v in labels:ans[next(c for c in range(k) if var(v,c) in model)].append(v)
    return [c for c in ans if c]

def main():
    p=ArgumentParser();p.add_argument("seed",type=Path);p.add_argument("result",type=Path);p.add_argument("--seconds",type=int,default=80)
    a=p.parse_args();base=Path(__file__).resolve().parent
    ref=runpy.run_path(str(base/"plane-color.py"));pairs=ref["pairs"];conflict=ref["conflict"];adj=ref["edge"]
    neighbors=[0]*len(pairs)
    for i,j in combinations(range(len(pairs)),2):
        if conflict(pairs[i],pairs[j]):neighbors[i]|=1<<j;neighbors[j]|=1<<i
    tests=json.loads(a.seed.read_bytes()); full=(1<<len(pairs))-1
    def mask(s):
        return sum(1<<i for i,(x,y) in enumerate(pairs) if x in s and y in s)
    masks=[mask(s) for s in tests];seen=set();rng=random.Random(51894)
    a.result.write_bytes((json.dumps(tests)+"\n").encode())
    end=time.monotonic()+a.seconds;iters=0
    while time.monotonic()<end:
        iters+=1
        r=rng.choices([3,4,5,6,7,8,9],[1,4,8,8,5,3,1])[0]
        gone=tuple(sorted(rng.sample(range(len(tests)),r)))
        if gone in seen:continue
        seen.add(gone);keep=[i for i in range(len(tests)) if i not in gone];un=full
        for i in keep:un&=~masks[i]
        colors=coloring(un,neighbors,r-1,1000,rng)
        if colors is None:continue
        new=[tests[i] for i in keep]+[sorted({v for j in cls for v in pairs[j]}) for cls in colors]
        assert all(all(not adj(u,v) for u,v in combinations(s,2)) for s in new)
        assert all(any(x in s and y in s for s in new) for x,y in pairs)
        print("repaired",iters,"families, size",len(new),flush=True)
        tests=new;masks=[mask(s) for s in tests];seen.clear()
        a.result.write_bytes((json.dumps(new)+"\n").encode())
    print('finished',iters,'neighborhoods, size',len(tests),flush=True)
if __name__=="__main__":main()
