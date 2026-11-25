"""Replay the six-input application of the smaller catalogue."""
from importlib import import_module
from pathlib import Path
import json
import subprocess
import sys

cat=import_module("catalogue")
truth=(4277074666<<32)+4274843776
table=cat.dual(6,truth)


def replay(binary,catalogue):
    library={}
    for r in catalogue:
        for t,_,_ in cat.images(r["inputs"],int(r["truth"],16)):
            library[r["inputs"],t]=r["binary_size"]
    domains=cat.constraints(6,table,library)
    data="".join(f"{rows:x} {cost}\n" for rows,cost,_ in domains)
    assert max(cost+fixed for _,cost,fixed in domains)==8
    check=subprocess.run([str(binary),"6",f"{table:x}","full","9","9","35","90000000"],
                         input=data,capture_output=True,text=True,check=True)
    print(check.stdout,end="")
    if "63 budget 9 UNSAT visits " not in check.stdout:
        raise RuntimeError("the nine-gate exclusion did not finish")
    # Ten-gate AND/OR circuit in the independently checked positive submission, PR 17601.
    gates=[[1,0,1],[1,0,4],[0,0,5],[0,6,4],[1,9,2],[1,7,5],[0,1,11],[1,12,3],[0,10,13],[1,8,14]]
    assert len(gates)==10 and cat.eval_gates(6,gates,2)==truth
    print("Ten-gate AND/OR witness verified on 64 assignments.")


if __name__=="__main__":
    replay(Path(sys.argv[1]).resolve(),json.loads(Path(__file__).with_name("circuits.json").read_bytes()))
