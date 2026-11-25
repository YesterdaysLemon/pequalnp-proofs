"""Generate witnesses for the finite signed-wire case split."""
from dataclasses import dataclass
from functools import cache
from itertools import combinations, permutations
from pathlib import Path
from collections import Counter
import json
import sys


@dataclass(frozen=True)
class Case:
    bank: tuple[int, ...]
    need: tuple[int, ...]


class Certificate:
    def __init__(self, labels, budget, minor_bounds=(), double_cliques=False):
        self.labels = tuple(labels)
        self.n = len(labels)
        self.width = 1 << self.n
        self.mask = (1 << self.width) - 1
        rows = [sum((x >> i & 1) << v for i, v in enumerate(labels)) for x in range(self.width)]
        target = [(x & 5 == 5 or x & 10 == 10 or x & 96 and x.bit_count() >= 2) for x in rows]
        self.y = sum(bool(t) << i for i, t in enumerate(target))
        self.negative = [x for x,t in enumerate(target) if not t]
        self.lits = tuple(sum((x >> i & 1) << x for x in range(self.width)) for i in range(self.n))
        self.minors = tuple(self.mask ^ w for w in self.lits) if minor_bounds else ()
        if double_cliques:
            self.minors += tuple(self.mask & ~(self.lits[i] | self.lits[j])
                                 for i, j in ((0, 2), (1, 3)))
            minor_bounds = tuple(minor_bounds) + (7, 7)
        self.initial = Case(self.lits, tuple(minor_bounds))
        self.budget = budget
        self.syms = []
        self.rowmaps = []
        self.chunks = []
        for p in permutations(range(self.n)):
            g = [sum((x >> i & 1) << p[i] for i in range(self.n)) for x in range(self.width)]
            if any(bool(target[x]) != bool(target[g[x]]) for x in range(self.width)): continue
            self.syms.append(p)
            self.rowmaps.append(g)
            table = []
            for base in range(0, self.width, 8):
                table.append(tuple(sum((b >> j & 1) << g[base+j] for j in range(8)) for b in range(256)))
            self.chunks.append(table)
        self.debt_order = []
        for g in range(len(self.syms)):
            images = [self.minors.index(self.acted(g, m)) for m in self.minors]
            self.debt_order.append([images.index(j) for j in range(len(self.minors))])
        self.states = [dict() for _ in range(budget+1)]
        self.stats = Counter()

    @cache
    def acted(self, g, w):
        return sum(tab[(w >> 8*i) & 255] for i,tab in enumerate(self.chunks[g]))

    def canonical(self, c):
        best = None
        for i, order in enumerate(self.debt_order):
            s = tuple(sorted(self.acted(i, w) for w in c.bank))
            entry = (s, tuple(c.need[j] for j in order), i)
            if best is None or entry < best: best = entry
        return Case(best[0],best[1]), best[2]

    @cache
    def cut(self, w):
        return sum(((self.mask ^ w if w >> x & 1 else w) & self.y) << (self.width * j)
                   for j,x in enumerate(self.negative))

    def valid(self, k, c):
        if k < 0 or len(c.bank) > k+1: return False
        for mask, req in zip(self.minors,c.need):
            if req + sum(w & mask == 0 for w in c.bank) > k: return False
        cover = 0
        for w in c.bank: cover |= self.cut(w)
        target = self.cut(self.y)
        return cover == target

    def children(self, k, c):
        for j,i in combinations(range(len(c.bank)),2):
            a,b = c.bank[j],c.bank[i]
            for op,z in enumerate((a & b, a | b, a & ~b, b & ~a)):
                if z == 0 or z in c.bank: continue
                need = []
                for mask,req in zip(self.minors,c.need):
                    sub = z & mask
                    old = sub == 0 or any(w & mask == sub for w in c.bank)
                    need.append(req if old else max(0,req-1))
                for hold in range(4):
                    keep = tuple(w for n,w in enumerate(c.bank) if
                                 (n != j or hold & 1) and (n != i or hold & 2))
                    child = Case(keep + (z,),tuple(need))
                    if not self.valid(k-1,child): continue
                    tag = ((j*16+i)*4+op)*4+hold
                    yield tag, child

    def visit(self, k, c):
        canon,g = self.canonical(c)
        table = self.states[k]
        if canon in table: return table[canon][0],g
        if self.y in canon.bank:
            raise AssertionError("a feasible gate generates the target")
        ix = len(table)
        arcs = []
        table[canon] = (ix,arcs)
        if k:
            for tag,child in self.children(k,canon):
                index,perm = self.visit(k-1,child)
                arcs.append((tag,index,perm))
        return ix,g

    def save(self, name):
        assert self.valid(self.budget,self.initial)
        index,perm = self.visit(self.budget,self.initial)
        entries = [[dict(bank=c.bank,need=c.need,arcs=arcs) for c,(i,arcs) in t.items()]
                   for t in self.states]
        obj = dict(name=name,labels=self.labels,initial=self.initial.bank,y=self.y,negative=self.negative,
                   masks=self.minors,syms=self.syms,rowmaps=self.rowmaps,depth=self.budget,
                   root=[index,perm],layers=entries)
        (Path(__file__).resolve().parent / f"seven-cert-{name}.json").write_text(json.dumps(obj,separators=(",",":")))
        print(name, "states",[len(l) for l in entries],"arcs",
              [sum(len(e['arcs']) for e in l) for l in entries],flush=True)

if __name__=="__main__":
    jobs = dict(clique=([1,3,5,6],6,()),private=([1,2,3,5,6],7,()), universal=([0,1,2,3,6],7,()),
                six=([0,1,2,3,5,6],10,(8,)*6,True))
    jobs["six-single"] = ([0,1,2,3,5,6],10,(8,)*6)
    for name in sys.argv[1:]:
        Certificate(*jobs[name]).save(name)
