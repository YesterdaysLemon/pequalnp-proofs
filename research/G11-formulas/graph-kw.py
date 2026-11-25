"""Monochromatic rectangle partitions for the edge versus independent-set game."""
from itertools import combinations

edges=[(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]

def structure(edges):
    n=max(v for e in edges for v in e)+1
    E=[(1<<a)|(1<<b) for a,b in edges]
    ind={x for x in range(1<<n) if all(x&e!=e for e in E)}
    columns=sorted(x for x in ind if all(x|1<<i not in ind for i in range(n) if not x>>i&1))
    patterns=[]
    for v in range(n):
        incident=[i for i,e in enumerate(E) if e>>v&1]
        for size in range(1,len(incident)+1):
            for rows in combinations(incident,size):
                patterns.append((v,rows,[j for j,c in enumerate(columns) if not c>>v&1]))
    return columns,patterns
