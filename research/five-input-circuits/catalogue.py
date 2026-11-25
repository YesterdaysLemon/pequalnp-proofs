"""Replay and look up the exact gate counts of all monotone functions on at most five inputs."""
from argparse import ArgumentParser
from collections import Counter
from itertools import permutations, product
from pathlib import Path
import json
import subprocess


def bit(t,r):
    return (t>>r)&1


def word(values):
    return sum(int(bool(v))<<i for i,v in enumerate(values))


def dual(n,t):
    last=(1<<n)-1
    return word(not bit(t,last^r) for r in range(last+1))


def minimal_true(n,t):
    return [r for r in range(1<<n) if bit(t,r) and all(
        not bit(t,r^(1<<i)) for i in range(n) if bit(r,i))]


def antichains(n):
    upper=[word((q&r)==r for q in range(1<<n)) for r in range(1<<n)]
    def generate(start,chosen,t):
        yield t
        for r in range(start,1<<n):
            if all((p&r) not in (p,r) for p in chosen):
                yield from generate(r+1,chosen+[r],t|upper[r])
    return generate(0,[],0)


def apply(op,x,y):
    return (x&y,x|y,x&~y,y&~x,x^y)[op]


def eval_gates(n,gates,limit):
    values=[word(bit(r,i) for r in range(1<<n)) for i in range(n)]
    for op,i,j in gates:
        assert 0<=op<limit and 0<=i<len(values) and 0<=j<len(values)
        values.append(apply(op,values[i],values[j]))
    return values[-1]


def images(n,t):
    for perm in permutations(range(n)):
        v=word(bit(t,sum(bit(r,p)<<i for i,p in enumerate(perm))) for r in range(1<<n))
        yield v,perm,False
        yield dual(n,v),perm,True


def essential(n,t):
    return [i for i in range(n) if any(bit(t,r)!=bit(t,r^(1<<i)) for r in range(1<<n))]


def embed(r,cols):
    return sum(bit(r,j)<<v for j,v in enumerate(cols))


def reduce_table(n,t):
    cols=essential(n,t)
    return cols,word(bit(t,embed(r,cols)) for r in range(1<<len(cols)))


def constraints(n,t,library):
    ds=[]
    for pins in product((-1,0,1),repeat=n):
        free=[i for i,b in enumerate(pins) if b<0]
        if not 0<len(free)<n:continue
        base=sum((b==1)<<i for i,b in enumerate(pins))
        rows=[base|embed(r,free) for r in range(1<<len(free))]
        cols,v=reduce_table(len(free),word(bit(t,r) for r in rows))
        if len(cols)>1:
            ds.append((sum(1<<r for r in rows),library[len(cols),v],n-len(free)))
    return ds


def exclude(binary,n,t,basis,cost,library,cap):
    if cost<=n-1:return "essential input count",0
    total=0
    for t0 in (t,dual(n,t)):
        ds=constraints(n,t0,library)
        if any(bound+fixed>=cost for _,bound,fixed in ds):
            return "restriction",total
        for domains in (30,14):
            k=cost-1
            proc=subprocess.run([str(binary),str(n),f"{t0:x}",basis,str(k),str(k),str(domains),str(cap)],
                input="".join(f"{rows:x} {c}\n" for rows,c,_ in ds),capture_output=True,text=True,check=True)
            words=proc.stdout.split()
            assert words[:3]==[str((1<<n)-1),"budget",str(k)], proc.stdout
            total+=int(words[5])
            if words[3]=="UNSAT":return "search",total
            if words[3]!="UNKNOWN":
                raise ValueError(f"smaller {basis} circuit for {t:x}: {proc.stdout}")
    raise RuntimeError(f"inconclusive search for {basis} on {t:x} at budget {cost-1}")


def verify(rows,binary,cap):
    orbit_cost={}
    for n in range(2,6):
        all_mono=set(antichains(n))
        assert len(all_mono)==[0,0,6,20,168,7581][n]
        covered=set()
        reasons=Counter()
        visits=0
        for rec in (v for v in rows if v["inputs"]==n):
            t=int(rec["truth"],16)
            group={w for w,_,_ in images(n,t)}
            assert min(group)==t and group<=all_mono and group.isdisjoint(covered)
            assert len(group)==rec["multiplicity"] and len(essential(n,t))==n
            m,f=rec["monotone_size"],rec["binary_size"]
            assert 0<f<=m and len(rec["monotone"])==m and eval_gates(n,rec["monotone"],2)==t
            witness=rec.get("binary",rec["monotone"])
            assert len(witness)==f and eval_gates(n,witness,5)==t
            if binary:
                why,count=exclude(binary,n,t,"full",f,orbit_cost,cap)
                reasons[why]+=1;visits+=count
                if f<m:
                    why,count=exclude(binary,n,t,"signed",m,orbit_cost,cap)
                    reasons["signed "+why]+=1;visits+=count
            for w in group:orbit_cost[n,w]=f
            covered.update(group)
        assert covered=={w for w in all_mono if len(essential(n,w))==n}
        print(f"{n} inputs, {len(covered)} labeled essential functions, {sum(r['inputs']==n for r in rows)} classes, {visits:,} search visits",dict(reasons),flush=True)
    sep=[r for r in rows if r["binary_size"]<r["monotone_size"]]
    assert len(rows)==110 and len(sep)==3 and sum(r["multiplicity"] for r in sep)==181


def transform(gates,perm,flip,cols,n):
    wires=[cols[j] for j in perm]
    signs=[flip]*len(cols)
    out=[]
    for op,i,j in gates:
        s=apply(op,int(signs[i]),int(signs[j]))&1
        vals=[(apply(op,x^int(signs[i]),y^int(signs[j]))&1)^s for x,y in product(range(2),repeat=2)]
        new=next(q for q in range(5) if [apply(q,x,y)&1 for x,y in product(range(2),repeat=2)]==vals)
        out.append([new,wires[i],wires[j]])
        signs.append(bool(s));wires.append(n+len(out)-1)
    assert signs[-1]==flip
    return out


def lookup(rows,n,t):
    if not 0<=n<=5 or t<0 or t.bit_length()>1<<n:raise ValueError("input or truth table out of range")
    cols,v=reduce_table(n,t)
    if not cols:return {"constant":bool(t),"size":0}
    if len(cols)==1:
        if v!=2:raise ValueError("truth table is not monotone")
        return {"input":cols[0],"size":0}
    for rec in (r for r in rows if r["inputs"]==len(cols)):
        for w,perm,flip in images(len(cols),int(rec["truth"],16)):
            if w!=v:continue
            mono=transform(rec["monotone"],perm,flip,cols,n)
            full=transform(rec.get("binary",rec["monotone"]),perm,flip,cols,n)
            assert eval_gates(n,mono,2)==t and eval_gates(n,full,5)==t
            return {"monotone_size":len(mono),"free_complement_size":len(mono),"binary_size":len(full),
                    "monotone_gates":mono,"binary_gates":full}
    raise ValueError("truth table is not monotone")


if __name__=="__main__":
    p=ArgumentParser()
    p.add_argument("catalogue",type=Path)
    p.add_argument("--binary",type=Path)
    p.add_argument("--cap",type=int,default=100000000)
    p.add_argument("--lookup",nargs=2,metavar=("INPUTS","HEX_TABLE"))
    args=p.parse_args()
    rows=json.loads(args.catalogue.read_bytes())
    if args.lookup:
        print(json.dumps(lookup(rows,int(args.lookup[0]),int(args.lookup[1],16)),indent=2))
    else:
        verify(rows,args.binary.resolve() if args.binary else None,args.cap)
