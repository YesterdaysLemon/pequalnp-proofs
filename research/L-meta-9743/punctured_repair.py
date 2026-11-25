"""Search nonlocal rewrites of 124-gate and mixed-center plane circuits."""
from pathlib import Path
from random import Random
import argparse
import json
import plane_search as ps
from plane_repair import repair


def configure():
    ps.LINES=tuple(tuple(p for p in ns if not (p==0 and l==0)) for l,ns in enumerate(ps.LINES))
    ps.POINTS=tuple(tuple(l for l,ns in enumerate(ps.LINES) if p in ns) for p in range(21))


def start(seed,mixed):
    rng=Random(731439+seed)
    out=[]
    def gate(op,a,b):
        out.append((op,a,b))
        return 41+len(out)
    def combine(ns):
        ns=list(ns)
        while len(ns)>1:
            a=ns.pop(rng.randrange(len(ns)))
            b=ns.pop(rng.randrange(len(ns)))
            ns.append(gate("or",a,b))
        return ns[0]
    es=[(p,l+21) for l,ns in enumerate(ps.LINES) for p in ns]
    if seed%2:
        es=[(l,p) for p,l in es]
    moved=set()
    if mixed:
        for v in rng.sample(sorted({q for _,q in es}),1+seed%3):
            candidates=[e for e in es if e[1]==v]
            moved.update(rng.sample(candidates,rng.randint(2,len(candidates))))
    stars={}
    for e in es:
        a,b=e[::-1] if e in moved else e
        stars.setdefault(a,[]).append(b)
    keys=list(stars);rng.shuffle(keys)
    combine(gate("and",v,combine(stars[v])) for v in keys)
    return out


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--seeds",type=int,default=12)
    ap.add_argument("--out",type=Path)
    args=ap.parse_args()
    configure()
    pos,neg=ps.boundary()
    full=ps.columns(pos+neg)
    sample=pos+Random(25836).sample(neg,1024)
    chips=ps.columns(sample);target=(1<<len(pos))-1
    print("flags",len(pos),"maximal negatives",len(neg),flush=True)
    for s in range(args.seeds):
        total=0
        for mixed in (False,True):
            gates=start(s,mixed)
            assert ps.evaluate(gates,full)[-1]==target
            found=ps.search(gates,chips,len(sample),target,2,
                            lambda c:ps.evaluate(c,full)[-1]==target,123)
            if not found and not mixed:
                for j,(_,a,b) in enumerate(gates,42):
                    for w in (a,b):
                        total+=1
                        found=repair(ps.replace(gates,j,w),chips,len(sample),target,full,123)
                        if found: break
                    if found: break
            if found:
                assert len(found)<=123 and ps.evaluate(found,full)[-1]==target
                if args.out: args.out.write_text(json.dumps(found)+"\n")
                print("FOUND",len(found),"seed",s,flush=True)
                return
        print("seed",s,"two starting circuits,",total,"extra deletions tested",flush=True)


if __name__=="__main__":
    main()
