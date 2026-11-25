"""Test circuits formed by a shared OR of inputs followed by a formula."""
from argparse import ArgumentParser
from collections import Counter
from importlib.util import module_from_spec,spec_from_file_location
from itertools import combinations
from pathlib import Path
import json
import sys

base=Path(__file__).resolve().parent
spec=spec_from_file_location("kw",base/"graph-kw.py")
kw=module_from_spec(spec);sys.dont_write_bytecode=True;spec.loader.exec_module(kw)

def build(S):
    pos=[(1<<a)|(1<<b) for a,b in kw.edges]
    cols,raw=kw.structure(kw.edges)
    A=[i for i,e in enumerate(pos) if S&e];B=[j for j,c in enumerate(cols) if not S&c]
    return build_for(pos,cols,raw,A,B,23-S.bit_count())

def build_for(pos,cols,raw,A,B,budget,*,linear_cells=False):
    if len(B)<=1:return "one column"
    variables=0;sel=[];cnf=[]
    def fresh():
        nonlocal variables
        variables+=1
        return variables
    cells=[[[] for _ in cols] for _ in pos]
    def pattern(rs,js,rowFixed):
        if not rs or not js:return
        s=fresh();sel.append(s)
        for v in (js if rowFixed else rs):
            b=fresh();cnf.append([-b,s])
            for u in (rs if rowFixed else js):
                (cells[u][v] if rowFixed else cells[v][u]).append(b)
    for _,rs,js in raw:pattern(rs,js,True)
    transpose=len(B)<len(A)
    small,big=(B,A) if transpose else (A,B)
    for x in range(1,1<<len(small)):
        sub=[v for l,v in enumerate(small) if x>>l&1]
        rs,js=(big,sub) if transpose else (sub,big)
        common=(1<<11)-1
        for i in rs:common&=pos[i]
        for j in js:common&=~cols[j]
        if common:continue
        pattern(rs,js,not transpose)
    for row in cells:
        for options in row:
            cnf.append(options)
            if linear_cells and len(options)>8:
                previous=options[0]
                for option in options[1:-1]:
                    current=fresh()
                    cnf.extend(([-previous,-option],[-previous,current],[-option,current]))
                    previous=current
                cnf.append([-previous,-options[-1]])
            else:
                cnf.extend([-a,-b] for a,b in combinations(options,2))
    previous=[]
    for selected in sel:
        following=[fresh() for _ in range(min(budget+1,len(previous)+1))]
        cnf.append([-selected,following[0]])
        for j,old in enumerate(previous):
            cnf.append([-old,following[j]])
            if j+1<len(following):cnf.append([-selected,-old,following[j+1]])
        previous=following
    if len(previous)>budget:cnf.append([-previous[budget]])
    return cnf

def main():
    from pysat.solvers import Solver
    ap=ArgumentParser(description=__doc__);ap.add_argument("out",type=Path);ap.add_argument("--cap",type=int,default=90000)
    ap.add_argument("--resume",action="store_true");args=ap.parse_args()
    out=json.loads(args.out.read_bytes()) if args.resume else {}
    for S in sorted(range(1,2048),key=lambda s:(s.bit_count(),s)):
        if S.bit_count()<2:continue
        key=str(S)
        if key in out and out[key]["status"]!="UNKNOWN":continue
        cnf=build(S)
        if isinstance(cnf,str):result={"status":cnf}
        else:
            with Solver(name="cadical195",bootstrap_with=cnf) as solver:
                solver.conf_budget(args.cap);v=solver.solve_limited()
                result={"status":"SAT" if v else ("UNKNOWN" if v is None else "UNSAT"),"conflicts":solver.accum_stats()["conflicts"]}
        out[key]=result
        if len(out)%10==0:
            tmp=args.out.with_suffix(".tmp");tmp.write_bytes(json.dumps(out,separators=(",",":")).encode());tmp.replace(args.out)
        if len(out)%60==0:print(len(out),Counter(x["status"] for x in out.values()),flush=True)
    args.out.write_bytes(json.dumps(out,separators=(",",":")).encode())
    print(len(out),Counter(x["status"] for x in out.values()),flush=True)

if __name__=="__main__":main()
