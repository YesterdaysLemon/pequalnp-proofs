"""Check boundary signatures which remain after charging to pure OR gates."""
import argparse
import json
from importlib.util import module_from_spec,spec_from_file_location
from pathlib import Path
import sys
from pysat.solvers import Solver

root=Path(__file__).resolve().parent
spec=spec_from_file_location("ext",root/"g11-shared-or.py");ext=module_from_spec(spec)
sys.dont_write_bytecode=True;spec.loader.exec_module(ext)

if __name__=="__main__":
    args=argparse.ArgumentParser();args.add_argument("candidates",type=Path);args.add_argument("output",type=Path)
    args.add_argument("--cap",type=int,default=95000);args.add_argument("--maximum",type=int,default=4);args.add_argument("--resume",action="store_true")
    args.add_argument("--linear",action="store_true",help="use a sequential counter on large cell-choice lists")
    a=args.parse_args()
    pos=[(1<<u)|(1<<v) for u,v in ext.kw.edges];cols,raw=ext.kw.structure(ext.kw.edges)
    result=json.loads(a.output.read_bytes()) if a.resume else {}
    for word,t in json.loads(a.candidates.read_bytes())["unresolved"].items():
        if t>a.maximum or (word in result and result[word]["status"]!="UNKNOWN"):continue
        w=int(word,16);A=[i for i in range(len(pos)) if w>>i&1];B=[j for j in range(len(cols)) if not w>>(len(pos)+j)&1]
        cnf=ext.build_for(pos,cols,raw,A,B,22-t,linear_cells=a.linear)
        if isinstance(cnf,str):r={"status":cnf}
        else:
            with Solver(name="cadical195",bootstrap_with=cnf) as s:
                s.conf_budget(a.cap);v=s.solve_limited()
                r={"status":"UNKNOWN" if v is None else ("SAT" if v else "UNSAT"),"conflicts":s.accum_stats()["conflicts"]}
                if a.linear:r["encoding"]="sequential"
        result[word]=r
        if len(result)%10==0:a.output.write_bytes(json.dumps(result,separators=(",",":")).encode())
        if len(result)%50==0:print(len(result),sum(r["status"]=="SAT" for r in result.values()),"SAT",flush=True)
    a.output.write_bytes(json.dumps(result,separators=(",",":")).encode())
    print("total",len(result),{q:sum(r["status"]==q for r in result.values()) for q in ["UNKNOWN","SAT","UNSAT","one column"]},flush=True)
