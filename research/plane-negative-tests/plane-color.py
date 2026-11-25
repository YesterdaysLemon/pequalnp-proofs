"""Turn universal negative tests for a graph into a graph coloring problem."""
from itertools import combinations
from pathlib import Path
import json, sys
V=42
D={0,5,7,17,20}
def edge(i,j):
    i,j=sorted((i,j))
    return i<21<=j and (j-i)%21 in D
pairs=[(i,j) for i,j in combinations(range(V),2) if not edge(i,j)]
def conflict(first,second):
    return any(edge(i,j) for i in first for j in second)
def main():
    tests=json.loads(Path(sys.argv[1]).read_bytes())
    source=Path(sys.argv[2])
    graph=[(a,b) for a,b in combinations(range(len(pairs)),2) if conflict(pairs[a],pairs[b])]
    owners=[next(k for k,t in enumerate(tests) if i in t and j in t) for i,j in pairs]
    lines=[f"{len(pairs)} {len(graph)} {len(tests)}"," ".join(map(str,owners))]+[f"{a} {b}" for a,b in graph]
    source.write_bytes(("\n".join(lines)+"\n").encode())
    print(len(pairs),"vertices",len(graph),"conflicts",flush=True)
if __name__=="__main__":main()
