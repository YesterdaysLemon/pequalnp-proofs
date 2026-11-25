"""Verify all labeled six-input monotone functions through the published gate-size cutoff."""
from collections import Counter
from itertools import product
from pathlib import Path
import argparse
import json
import subprocess
import sys

here=Path(__file__).resolve().parent
sys.path.insert(0,str(here.parent/"five-input-circuits"))
import catalogue as cat


def bases(rows):
    raw={(0,0):(0,0),(0,1):(0,0),(1,2):(0,0)}
    for r in rows:
        for t,_,_ in cat.images(r["inputs"],int(r["truth"],16)):
            raw[r["inputs"],t]=r["binary_size"],r["monotone_size"]
    result={}
    for n in range(1,6):
        for t in cat.antichains(n):
            cols,v=cat.reduce_table(n,t)
            result[n,t]=raw[len(cols),v]
    return result


def subcubes():
    layouts=[]
    for pins in product((-1,0,1),repeat=6):
        free=[i for i,b in enumerate(pins) if b<0]
        if not 1<len(free)<6:continue
        fixed=sum((b==1)<<i for i,b in enumerate(pins))
        rows=[fixed|cat.embed(x,free) for x in range(1<<len(free))]
        layouts.append((len(free),rows,sum(1<<r for r in rows)))
    return sorted(layouts,key=lambda item:-item[0])


def need(t,mode,k,small,layouts):
    constraints=[]
    for n,rows,mask in layouts:
        word=sum(((t>>r)&1)<<j for j,r in enumerate(rows))
        cost=small[n,word][0 if mode=="full" else 1]
        if not cost:continue
        if cost+6-n>=k:return None
        constraints.append((mask,cost))
    return constraints


def exclude(t,basis,cost,binary,small,layouts,cap):
    if cost<=5:return 0
    visits=0
    for w in (t,cat.dual(6,t)):
        ds=need(w,basis,cost,small,layouts)
        if ds is None:return visits
        k=cost-1
        for d in (32,16):
            result=subprocess.run([str(binary),"6",f"{w:x}",basis,str(k),str(k),str(d),str(cap)],
                input="".join(f"{mask:x} {bound}\n" for mask,bound in ds),capture_output=True,text=True,check=True)
            parts=result.stdout.split()
            assert parts[:3]==["63","budget",str(k)]
            visits+=int(parts[5])
            if parts[3]=="UNSAT":return visits
            if parts[3]!="UNKNOWN":raise ValueError(f"counterexample to the stored {basis} bound for {t:x} at {k}")
    raise RuntimeError(f"inconclusive {basis} search for {t:x} at {cost-1}")


def verify(five,book,binary,orbit,cap):
    small=bases(five)
    words=sorted(cat.antichains(5))
    listing=subprocess.run([str(orbit)],input="".join(f"{w:x}\n" for w in words),
                           capture_output=True,text=True,check=True)
    print(listing.stderr.strip(),flush=True)
    ceiling=book["through"]
    stored={r["truth"]:r for r in book["classes"]}
    assert len(stored)==len(book["classes"])
    layouts=subcubes();classes=Counter();labeled=Counter();visits=0
    for line in listing.stdout.splitlines():
        key,multiplicity=line.split();mult=int(multiplicity);t=int(key,16)
        rec=stored.pop(key,None)
        f=s=m=ceiling+1
        if rec:
            assert rec["multiplicity"]==mult
            f,s,m=rec["sizes"]
            assert 5<=f<=s<=m<=ceiling+1 and f<=ceiling
            for label,size,maximum in [("mono",m,2),("signed",s,4),("full",f,5)]:
                if size>ceiling:continue
                gates=rec.get(label,rec.get("signed",rec.get("mono")))
                assert len(gates)==size and cat.eval_gates(6,gates,maximum)==t
        visits+=exclude(t,"full",f,binary,small,layouts,cap)
        if s>f:visits+=exclude(t,"signed",s,binary,small,layouts,cap)
        if m>s:visits+=exclude(t,"mono",m,binary,small,layouts,cap)
        for name,size in [("full",f),("signed",s),("mono",m)]:
            classes[name,size]+=1;labeled[name,size]+=mult
    assert not stored
    for k in range(5,ceiling+2):
        print(("above cutoff" if k==ceiling+1 else f"size {k}"),[(b,classes[b,k],labeled[b,k]) for b in ("mono","signed","full")],flush=True)
    print(f"{visits:,} bounded-search visits. All exclusions and witnesses checked.",flush=True)


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("search",type=Path)
    p.add_argument("orbits",type=Path)
    p.add_argument("--cap",type=int,default=100000000)
    args=p.parse_args()
    verify(json.loads((here.parent/"five-input-circuits/circuits.json").read_bytes()),
           json.loads((here/"frontier.json").read_bytes()),args.search.resolve(),args.orbits.resolve(),args.cap)
