"""Replay positive witnesses and check the shape of the induced-subgraph certificates."""
import argparse
import re
from pathlib import Path

EDGES = [(0,2),(1,3),(0,4),(1,4),(2,4),(0,5),(1,5),(3,5),(0,6),(2,6),(3,6),(5,6)]


def essential(subset):
    return {v for edge in EDGES if set(edge) <= subset for v in edge}


def replay(mask, circuit, mode):
    labels = [i for i in range(7) if mask & (1<<i)]
    for assignment in range(1<<len(labels)):
        chosen = {v for i,v in enumerate(labels) if assignment>>i&1}
        expected = bool(essential(chosen))
        wires = [v in chosen for v in labels]
        for op,a,b in circuit:
            assert 0 <= a < len(wires) and 0 <= b < len(wires)
            assert 0 <= op < (2 if mode=="mono" else 4)
            u,v = wires[a],wires[b]
            wires.append((u and v,u or v,u and not v,v and not u)[op])
        assert wires[-1] == expected


def read(path, mode):
    nodes = [m for m in range(1,128) if set(i for i in range(7) if m>>i&1) ==
              essential({i for i in range(7) if m>>i&1})]
    trials = {m:{} for m in nodes}
    bounds = {}
    for line in Path(path).read_text().splitlines():
        if line.startswith("lower "):
            _,m,value=line.split()
            assert int(m) not in bounds
            bounds[int(m)] = int(value)
            continue
        case = re.fullmatch(r"(\d+) budget (\d+) (SAT|UNSAT|UNKNOWN) visits (\d+)(?: gates(.*))?",line)
        assert case, line
        m,k,verdict = int(case[1]),int(case[2]),case[3]
        assert k not in trials[m] and int(case[4]) > 0
        trials[m][k] = verdict
        if verdict == "SAT":
            gates = [tuple(map(int,entry.split(","))) for entry in case[5].split()]
            assert len(gates) <= k
            replay(m,gates,mode)
    assert set(bounds) == set(nodes)
    for m in sorted(nodes,key=int.bit_count):
        n=m.bit_count()
        start=max([n-1]+[bounds[m^(1<<i)]+1 for i in range(7)
                          if m>>i&1 and m^(1<<i) in bounds])
        assert set(range(start,bounds[m])) <= {k for k,v in trials[m].items() if v=="UNSAT"}
        if m!=127:
            assert trials[m][bounds[m]] == "SAT"
    print(mode, len(nodes), "nonempty induced graphs with all selected vertices essential")
    print("full graph", sorted(trials[127].items()), "lower bound",bounds[127])


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode",choices=["mono","signed"])
    parser.add_argument("log")
    args=parser.parse_args()
    read(args.log,args.mode)
