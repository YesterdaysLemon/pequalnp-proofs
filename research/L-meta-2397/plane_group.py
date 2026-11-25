"""Construct the projective collineations and dualities of the Singer-labelled plane."""
from itertools import product
from pathlib import Path
import sys


def normalized(v):
    k=next((x for x in v if x),0)
    return tuple(x*k%3 for x in v)


def act(m,v):
    return normalized(tuple(sum(m[3*i+j]*v[j] for j in range(3))%3 for i in range(3)))


def group():
    matrices=[]
    singer=None
    for m in product(range(3),repeat=9):
        if next((x for x in m if x),0)!=1:
            continue
        a,b,c,d,e,f,g,h,i=m
        if (a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g))%3==0:
            continue
        matrices.append(m)
        if singer is None:
            orbit=[(1,0,0)]
            for _ in range(12):
                orbit.append(act(m,orbit[-1]))
            if len(set(orbit))!=13 or act(m,orbit[-1])!=orbit[0]:
                continue
            line=[orbit[i] for i in (0,1,3,9)]
            if any(any(n) and all(sum(x*y for x,y in zip(n,v))%3==0 for v in line)
                   for n in product(range(3),repeat=3)):
                singer=orbit
    assert singer is not None and len(matrices)==5616
    line=[frozenset((l+d)%13 for d in (0,1,3,9)) for l in range(13)]
    lines={v:k for k,v in enumerate(line)}
    out=[]
    for m in matrices:
        pi=[singer.index(act(m,v)) for v in singer]
        li=[lines[frozenset(pi[x] for x in pts)] for pts in line]
        out.append(bytes(pi+[13+x for x in li]))
        out.append(bytes([13+(-x)%13 for x in pi]+[(-x)%13 for x in li]))
    assert len(set(out))==11232
    return b"".join(out)


if __name__=="__main__":
    destination=Path(sys.argv[1])
    data=group()
    destination.write_bytes(data)
    print(len(data)//26,"permutations",flush=True)
