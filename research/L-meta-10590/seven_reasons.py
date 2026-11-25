"""Assign one checkable row or one cofactor obstruction to each unlinked child."""
from collections import Counter
from itertools import combinations
import json
from pathlib import Path
import sys

base=Path(__file__).resolve().parent

def encode(name):
    source=json.loads((base/f"seven-cert-{name}.json").read_text())
    y,neg,masks=source["y"],source["negative"],source["masks"]
    dictionary={0:0}
    output=[]
    uses=Counter()
    for k,layer in enumerate(source["layers"]):
        result=[]
        for e in layer:
            bank=e["bank"]
            linked={tag for tag,_,_ in e["arcs"]}
            groups=[]
            for i,j in combinations(range(len(bank)),2):
                a,b=bank[i],bank[j]
                opts=[set() for _ in range(16)]
                for op,z in enumerate((a&b,a|b,a&~b,b&~a)):
                    if not z or z in bank: continue
                    ds=[d if not z&m or any(w&m==z&m for w in bank) else max(0,d-1)
                        for m,d in zip(masks,e["need"])]
                    for hold in range(4):
                        keep=[w for q,w in enumerate(bank) if (q!=i or hold&1) and (q!=j or hold&2)]+[z]
                        if len(keep)>k: continue
                        tag=((i*16+j)*4+op)*4+hold
                        if tag in linked: continue
                        opt=opts[op*4+hold]
                        for h,row in enumerate(neg):
                            poss=y
                            for w in keep:
                                poss &= w if w>>row&1 else ~w
                                if not poss: break
                            if poss: opt.add(h)
                        for v,(m,d) in enumerate(zip(masks,ds)):
                            if d+sum(w&m == 0 for w in keep)>k-1: opt.add(len(neg)+v)
                        assert opt,(name,k,i,j,op,hold)
                chosen=[None]*16
                wanted={i for i,v in enumerate(opts) if v}
                default=0
                while wanted:
                    freq=Counter(q for i in wanted for q in opts[i])
                    reason=max(freq, key=lambda q: (freq[q], int(q<len(neg)), -q))
                    if all(x is None for x in chosen): default=reason
                    for t in list(wanted):
                        if reason in opts[t]:
                            wanted.remove(t)
                            chosen[t]=reason
                pat=sum((default if v is None else v) << (5*i) for i,v in enumerate(chosen))
                if pat not in dictionary: dictionary[pat]=len(dictionary)
                ix=dictionary[pat]
                groups.append(ix);uses[ix]+=1
            result.append(groups)
        output.append(result)
    width=max(1,(len(dictionary)-1).bit_length())
    data=dict(width=width,patterns=list(dictionary),groups=output)
    (base/f"seven-reasons-{name}.json").write_text(json.dumps(data,separators=(",",":")))
    print(name, "patterns",len(dictionary),"pairs",sum(uses.values()),"bits per index",width,
          "hex chars", sum((len(g)*width+3)//4 for l in output for g in l)+len(dictionary)*20,flush=True)

for name in sys.argv[1:]: encode(name)
