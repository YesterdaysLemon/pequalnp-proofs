"""Exact circuit sizes for Boolean truth tables under signed input permutations."""
from argparse import ArgumentParser
from collections import Counter
from functools import lru_cache
from itertools import product
from pathlib import Path
import json
import subprocess
import sys

def vars_(n):
    return [sum(1<<r for r in range(1<<n) if r>>i&1) for i in range(n)]


@lru_cache(None)
def orbits(n):
    mask = (1<<(1<<n))-1
    variables = vars_(n)
    swaps = [(1<<i,variables[i+1]&~variables[i]) for i in range(n-1)]
    def moves(t):
        for i,v in enumerate(variables):
            shift = 1<<i
            yield ((t&v)>>shift) | ((t&~v)<<shift)
        for shift,upper in swaps:
            lower = upper >> shift
            yield (t&~(upper|lower)) | ((t&upper)>>shift) | ((t&lower)<<shift)
    seen=set()
    result=[]
    for t in range(0,mask+1,2):
        if t in seen: continue
        seen.add(t)
        todo=[t]
        at=0
        while at<len(todo):
            for v in moves(todo[at]):
                v = v^mask if v&1 else v
                if v not in seen:
                    seen.add(v)
                    todo.append(v)
            at+=1
        result.append((t,todo))
    assert 2*len(seen)==mask+1
    return result


def subwords(n,t):
    free = [i for i in range(n) if any(((t>>r)^(t>>(r^(1<<i))))&1 for r in range(1<<n))]
    small = sum((t>>sum(((a>>j)&1)<<v for j,v in enumerate(free))&1)<<a for a in range(1<<len(free)))
    return len(free),small


def faces(n):
    out=[]
    for pins in product((-1,0,1),repeat=n):
        free=[i for i,b in enumerate(pins) if b<0]
        if not 1<len(free)<n:continue
        offset=sum((b==1)<<i for i,b in enumerate(pins))
        rows=[offset | sum(((r>>j)&1)<<v for j,v in enumerate(free)) for r in range(1<<len(free))]
        out.append((len(free),rows,sum(1<<r for r in rows)))
    return out


def evaluate(n,gates,model):
    bank=vars_(n)
    for op,i,j in gates:
        assert i<len(bank) and j<len(bank) and 0<=op<(5 if model=="full" else 4)
        a,b=bank[i],bank[j]
        bank.append((a&b,a|b,a&~b,b&~a,a^b)[op])
    return bank[-1]


def search(n,t,basis,binary,ds,part,limit,ceiling):
    key=2 if basis=="full" else 3
    low=max([part["lower"],n-1]+[d[key]+n-d[0] for d in ds if d[key]])
    high=min(ceiling,len(part["gates"])-1 if "gates" in part else ceiling)
    part["lower"]=low
    if high<low:return 0
    proc=subprocess.run([str(binary),str(n),f"{t:x}",basis,str(low),str(high),"48",str(limit)],
              input="".join(f"{d[1]:x} {d[key]}\n" for d in ds if d[key]),capture_output=True,text=True,check=True)
    visits=0
    for line in proc.stdout.splitlines():
        h=line.split()
        k=int(h[2]);visits+=int(h[5])
        assert h[:2]==[str((1<<n)-1),"budget"] and k==part["lower"]
        if h[3]=="UNSAT":part["lower"]=k+1
        elif h[3]=="SAT":
            g=[list(map(int,op.split(","))) for op in h[7:]]
            assert len(g)==k and evaluate(n,g,basis)==t
            part["gates"]=g
        else:assert h[3]=="UNKNOWN"
    return visits


def save(file,book):
    tmp=file.with_suffix(".tmp")
    tmp.write_bytes(json.dumps(book,separators=(",",":")).encode())
    tmp.replace(file)


def main():
    p=ArgumentParser(description=__doc__)
    p.add_argument("binary",type=Path)
    p.add_argument("data",type=Path)
    p.add_argument("--cap",type=int,default=2000000)
    p.add_argument("--ceiling",type=int,default=13)
    p.add_argument("--resume",action="store_true")
    p.add_argument("--compare",type=Path,help="verify a published catalogue against a fresh run")
    args=p.parse_args()
    book=json.loads(args.data.read_bytes()) if args.resume else {}
    known={(n,t):(0,0) for n in (0,1) for t in range(1<<(1<<n))}
    for n in (2,3,4):
        layout=faces(n)
        mask=(1<<(1<<n))-1
        visits=0;open_=0
        section=book.setdefault(str(n),{})
        for t,orbit in orbits(n):
            dims,w=subwords(n,t)
            if dims<n: result=known[dims,w]
            else:
                part=section.setdefault(f"{t:x}",{m:{"lower":n-1} for m in ("full","signed")})
                ds=[]
                for q,rows,domain in layout:
                    sub=sum(((t>>r)&1)<<j for j,r in enumerate(rows))
                    ds.append((q,domain,*known[q,sub]))
                for m in ("full","signed"):
                    if m=="signed":part[m]["lower"]=max(part[m]["lower"],part["full"]["lower"])
                    if part[m].get("gates") is None or len(part[m]["gates"])!=part[m]["lower"]:
                        visits+=search(n,t,m,args.binary,ds,part[m],args.cap,args.ceiling)
                    if m=="full" and "gates" in part[m] and all(g[0]<4 for g in part[m]["gates"]):
                        part["signed"]["gates"]=part[m]["gates"]
                if "gates" in part["signed"] and len(part["signed"]["gates"])<len(part["full"].get("gates",[0]*100)):
                    part["full"]["gates"]=part["signed"]["gates"]
                if any(part[m]["lower"]!=len(part[m].get("gates",[])) for m in ("signed","full")): open_+=1
                for m in ("full","signed"):
                    if "gates" in part[m]:
                        assert part[m]["lower"]<=len(part[m]["gates"]) and evaluate(n,part[m]["gates"],m)==t
                result=part["full"]["lower"],part["signed"]["lower"]
                if len(section)%12==0:save(args.data,book)
            for v in orbit:
                known[n,v]=known[n,v^mask]=result
        save(args.data,book)
        print(n,"inputs",len(section),"essential classes",open_,"unresolved",visits,"visits",flush=True)
        if n<4 and open_:raise RuntimeError("Complete the smaller catalogue first")
        if not open_:
            print("sizes",dict(sorted(Counter(known[n,t] for t in range(mask+1)).items())),flush=True)
    if args.compare:
        reference=json.loads(args.compare.read_bytes())
        assert set(book)==set(reference)
        total=0
        for ns,records in book.items():
            assert set(reference[ns])==set(records)
            for key,item in records.items():
                for mode in ("full","signed"):
                    wanted=reference[ns][key][mode]
                    assert evaluate(int(ns),wanted["gates"],mode)==int(key,16)
                    assert wanted["lower"]==len(wanted["gates"])==item[mode]["lower"]==len(item[mode]["gates"])
                    total+=1
        print(total,"minimum-size witnesses and their lower bounds verified")


if __name__=="__main__":main()
