"""Depth-limited decision-tree bounds on the unique-axiom assignments of PHP."""
from functools import cache
from itertools import combinations, permutations
import argparse


def critical(n):
    cases=[]
    def vector(pairs):
        return sum(1<<(p*n+h) for p,h in pairs)
    for missing in range(n+1):
        pigeons=[i for i in range(n+1) if i!=missing]
        cases.append([vector(zip(pigeons,hs)) for hs in permutations(range(n))])
    for a,b in combinations(range(n+1),2):
        for h in range(n):
            others=[i for i in range(n+1) if i not in (a,b)]
            holes=[i for i in range(n) if i!=h]
            cases.append([vector([(a,h),(b,h)]+list(zip(others,hs))) for hs in permutations(holes)])
    return cases


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("n",type=int)
    ap.add_argument("--depth",type=int,default=3)
    args=ap.parse_args()
    n=args.n
    cases=critical(n)
    labels=[]
    cuts=[0]*(n*(n+1))
    count=0
    for group in cases:
        labels.append(((1<<len(group))-1)<<count)
        for assignment in group:
            for v in range(len(cuts)):
                if assignment>>v & 1:
                    cuts[v]|=1<<count
            count+=1
    root=(1<<count)-1
    @cache
    def different(state):
        return sum(bool(state&mask) for mask in labels)
    @cache
    def depth_bound(state,depth):
        baseline=different(state)
        if depth==0 or baseline<=1:
            return baseline
        scores=(depth_bound(hi,depth-1)+depth_bound(state^hi,depth-1)
                for mask in cuts if (hi:=state&mask) and hi!=state)
        return min(scores)
    # All choices of the first bit are conjugate under row and column permutations.
    print("depth 0",len(labels),"distinct labels on",count,"assignments")
    for d in range(1,args.depth+1):
        a,b=depth_bound(root^cuts[0],d-1),depth_bound(cuts[0],d-1)
        print("depth",d,"lower leaves",a+b,"root children",a,b,
              "lines with shared axioms only",len(labels)+a+b-1,flush=True)


if __name__=="__main__":
    main()
