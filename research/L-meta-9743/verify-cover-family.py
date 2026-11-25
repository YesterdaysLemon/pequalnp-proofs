"""Rebuild the finite minimum-counterexample test for matching number at most five."""
from argparse import ArgumentParser
from pathlib import Path
import json
import os
import subprocess
import sys
from cover_audit import audit
from five_cover import run as five
from four_cover import run as four
from multi_data import write as make_probes


def verify(out,cxx):
    src=Path(__file__).resolve().parent
    out.mkdir(parents=True,exist_ok=True)
    binary=(out/"cover-checker").resolve()
    subprocess.run([cxx,"-O3","-std=c++20",str(src/"multi_search.cpp"),"-o",str(binary)],check=True)
    report=[]
    for label,gen in [("four",four),("five",five)]:
        dest=out/label
        gen(dest)
        cases=json.loads((dest/"cores.json").read_text())
        for k in sorted({c["k"] for c in cases}):audit(cases,k)
        make_probes(dest,2,set())
        for case in cases:
            with (dest/(case["name"]+".multi")).open() as problem:
                res=subprocess.run([str(binary),"250000000"],stdin=problem,text=True,
                                   capture_output=True,check=True).stdout.strip()
            if not res.startswith("UNSAT "):raise SystemExit(f"{case['name']}: {res}")
            report.append({"matching":case["k"],"case":case["name"],"vertices":case["vertices"],
                           "edges":len(case["edges"]),"minimum_gates":case["bound"],"visits":int(res.split()[2])})
        print("checked",len(cases),label,"catalogue entries",flush=True)
    (out/"replay.json").write_text(json.dumps(report,indent=1)+"\n")
    print("verified",len(report),"finite cores",flush=True)


if __name__=="__main__":
    parser=ArgumentParser(description=__doc__)
    parser.add_argument("directory",type=Path)
    parser.add_argument("--cxx",default=os.environ.get("CXX","c++"))
    options=parser.parse_args()
    verify(options.directory,options.cxx)
