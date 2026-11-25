"""Look up any Boolean function on at most four input positions."""
from argparse import ArgumentParser
from itertools import permutations
from pathlib import Path
import json


def lookup(n,t,book):
    if not 0<=n<=4 or not 0<=t<1<<(1<<n):raise ValueError("truth table must fit the given number of inputs")
    used=[i for i in range(n) if any(((t>>r)^(t>>(r^(1<<i))))&1 for r in range(1<<n))]
    m=len(used); words=1<<m
    if m<2:
        return {"essential_inputs":used,"full":0,"signed":0,"primary":used[0] if used else None,"invert":bool(t&1)}
    labels=lambda r:sum(((r>>j)&1)<<v for j,v in enumerate(used))
    small=sum(((t>>labels(r))&1)<<r for r in range(words))
    candidates=book[str(m)]
    for perm in permutations(range(m)):
        for flips in range(words):
            def old(new):return sum((((new^flips)>>j)&1)<<v for j,v in enumerate(perm))
            neg=(small>>old(0))&1
            rep=sum((((small>>old(r))&1)^neg)<<r for r in range(words))
            item=candidates.get(f"{rep:x}")
            if item is None:continue
            return {"essential_inputs":used,"representative":f"{rep:x}",
                    "representative_inputs":[[used[v],bool((flips>>j)&1)] for j,v in enumerate(perm)],
                    "complement_output":bool(neg),**item}
    raise ValueError("catalogue is incomplete")


if __name__=="__main__":
    p=ArgumentParser(description=__doc__)
    p.add_argument("inputs",type=int)
    p.add_argument("hex_table",help="bit r is the output on binary assignment r")
    a=p.parse_args()
    data=json.loads(Path(__file__).with_name("circuits.json").read_bytes())
    print(json.dumps(lookup(a.inputs,int(a.hex_table,16),data),indent=2))
