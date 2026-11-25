"""Construct CP refutations using a growing clique or a searched last hole."""
import argparse
from importlib.util import module_from_spec, spec_from_file_location
from itertools import combinations
from pathlib import Path

base = Path(__file__).resolve().parent
for source in (base / "cp-witness.py", base.parent / "L-meta-9668" / "cp-witness.py"):
    if source.is_file():
        spec = spec_from_file_location("cp_witness", source)
        previous = module_from_spec(spec)
        spec.loader.exec_module(previous)
        break
else:
    raise FileNotFoundError("cp-witness.py")


class Pigeon(previous.Derivation):
    def __init__(self, holes):
        super().__init__()
        self.holes = holes
        self.pigeons = holes + 1

    def ax(self, kind, *args):
        h = self.holes
        v = [0] * (h * self.pigeons)
        if kind == "row":
            p, = args
            for j in range(h):
                v[p*h+j] = -1
            rhs = -1
        elif kind == "hole":
            p, q, j = args
            assert p < q
            v[p*h+j] = v[q*h+j] = 1
            rhs = 1
        else:
            raise ValueError(kind)
        return self.record(v, rhs, (kind, *args))

    def edges(self, j):
        return {(p,q): self.ax("hole",p,q,j) for p,q in combinations(range(self.pigeons),2)}

    def clique(self, edges):
        line = edges[0,1]
        for p in range(2,self.pigeons):
            if p > 2:
                line = self.unary("mul",p-1,line)
            line = self.sum([line] + [edges[q,p] for q in range(p)])
            line = self.unary("div",p,line)
        return line

    def run(self, local=None):
        caps = [self.clique(self.edges(j)) for j in range(self.holes-1)]
        need = self.sum(caps + [self.ax("row",p) for p in range(self.pigeons)])
        edges = self.edges(self.holes-1)
        if local is None:
            self.plus(need,self.clique(edges))
        else:
            lines = local.read_text().splitlines()
            events = [(int(t[1]),int(t[2]),int(t[3]),int(t[4])) for t in
                      (line.split() for line in lines) if t and t[0] == "event"]
            buckets = [[] for _ in range(len(events)+1)]
            row = next(int(s.split()[1]) for s in lines if s.startswith("row "))
            allocation = next(list(map(int,s.split()[1:])) for s in lines if s.startswith("edges "))
            assert len(allocation) == len(edges)
            buckets[row].append(need)
            for e, b in zip(edges.values(),allocation):
                buckets[b].append(e)
            for i,f,p,q in reversed(events):
                value = self.sum(buckets[i])
                if f != 1:
                    value = self.unary("div" if f < 0 else "mul",abs(f),value)
                buckets[p].append(value)
                if q >= 0:
                    buckets[q].append(value)
            self.sum(buckets[0])
        assert self.lines[-1] == ((0,)*(self.pigeons*self.holes),-1)
        return self


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--holes",type=int,default=4)
    parser.add_argument("--local",type=Path)
    parser.add_argument("--out",required=True,type=Path)
    args = parser.parse_args()
    assert args.holes >= 2
    derivation = Pigeon(args.holes).run(args.local)
    previous.write_lean(derivation,args.out,"PigeonCapacity")
    source = args.out.read_text(encoding="utf-8")
    for old, new in (("Fin 4 × Fin 3", f"Fin {args.holes+1} × Fin {args.holes}"),
                     ("PHP 4 3", f"PHP {args.holes+1} {args.holes}"),
                     ("(i : Fin 4)",f"(i : Fin {args.holes+1})"),
                     ("(i j : Fin 4)",f"(i j : Fin {args.holes+1})"),
                     ("h : Fin 3",f"h : Fin {args.holes}")):
        source = source.replace(old,new)
    args.out.write_bytes(source.encode())
    print(f"PHP({args.holes+1},{args.holes}) refutation with {len(derivation.ops)} lines")
