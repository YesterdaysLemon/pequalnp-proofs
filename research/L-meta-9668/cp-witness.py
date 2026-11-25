"""Build and independently check concrete cutting-plane refutations of PHP(4,3)."""
import argparse
from itertools import combinations
from pathlib import Path
import re

ROOT=Path(__file__).resolve().parent
PAIRS=list(combinations(range(4),2))


class Derivation:
    def __init__(self):
        self.lines=[]
        self.ops=[]

    def record(self,v,r,op):
        self.lines.append((tuple(v),r))
        self.ops.append(op)
        return len(self.lines)-1

    def ax(self,op,*args):
        v=[0]*12
        if op=="row":
            p,=args
            for h in range(3): v[3*p+h]=-1
            r=-1
        elif op=="hole":
            p,q,h=args
            v[3*p+h]=v[3*q+h]=1
            r=1
        elif op=="bool":
            p,h,sign=args
            v[3*p+h]=sign
            r=int(sign==1)
        else: raise ValueError(op)
        return self.record(v,r,(op,*args))

    def plus(self,a,b):
        u,r=self.lines[a];v,s=self.lines[b]
        return self.record([x+y for x,y in zip(u,v)],r+s,("add",a,b))

    def sum(self,args):
        a,*rest=args
        for b in rest:a=self.plus(a,b)
        return a

    def unary(self,which,d,a):
        v,r=self.lines[a]
        if which=="div":
            assert d>0 and all(x%d==0 for x in v)
            return self.record([x//d for x in v],r//d,("div",d,a))
        assert which=="mul" and d>=0
        return self.record([x*d for x in v],r*d,("mul",d,a))

    def finish(self):
        assert self.lines[-1]==((0,)*12,-1),self.lines[-1]
        return self


def regular():
    d=Derivation()
    caps=[]
    for h in range(3):
        edges={(a,b):d.ax("hole",a,b,h) for a,b in PAIRS}
        triangle=d.sum([edges[0,1],edges[0,2],edges[1,2]])
        clique=d.unary("div",2,triangle)
        weight=d.unary("mul",2,clique)
        combined=d.sum([weight,edges[0,3],edges[1,3],edges[2,3]])
        caps.append(d.unary("div",3,combined))
    d.sum(caps+[d.ax("row",p) for p in range(4)])
    return d.finish()


def from_log(path):
    text=Path(path).read_text()
    n=int(re.search(r"FOUND events (\d+)",text)[1])
    definitions={}
    for i,f,p,q in re.findall(r"^event (\d+) (-?\d+) (\d+) (-?\d+)$",text,re.M):
        definitions[int(i)]=tuple(map(int,(f,p,q)))
    buckets=[[] for _ in range(n+1)]
    d=Derivation()
    for p,b in enumerate(re.search(r"^rows (.*)$",text,re.M)[1].split()):
        buckets[int(b)].append(d.ax("row",p))
    for h,line in enumerate(re.findall(r"^hole (.*)$",text,re.M)):
        for (u,v),b in zip(PAIRS,line.split()):
            buckets[int(b)].append(d.ax("hole",u,v,h))
    for p,h,s,b in re.findall(r"^bool (\d+) (\d+) (-?\d+) (\d+)$",text,re.M):
        buckets[int(b)].append(d.ax("bool",int(p),int(h),int(s)))
    for i in range(n,0,-1):
        f,p,q=definitions[i]
        ix=d.sum(buckets[i])
        if f!=1: ix=d.unary("div" if f<0 else "mul",abs(f),ix)
        buckets[p].append(ix)
        if q>=0:buckets[q].append(ix)
    d.sum(buckets[0])
    return d.finish()


def write_lean(derivation,out,namespace):
    head=f"""import PEqualNP.Defs

namespace {namespace}
open PEqualNP.Search PEqualNP.ProofComplexity
abbrev V := Fin 4 × Fin 3
abbrev F := PHP 4 3
abbrev L := CPLine V

def row (i : Fin 4) : Clause V := Finset.univ.image (fun h : Fin 3 => ((i,h),true))
def pair (i j : Fin 4) (h : Fin 3) : Clause V := {{((i,h),false),((j,h),false)}}
theorem row_mem (i : Fin 4) : row i ∈ F := Or.inl ⟨i,rfl⟩
theorem pair_mem (i j : Fin 4) (h : Fin 3) (ne : i ≠ j) : pair i j h ∈ F :=
  Or.inr ⟨i,j,h,ne,rfl⟩

def add (a b : L) : L := (a.1 + b.1,a.2 + b.2)
def mul (n : ℕ) (a : L) : L := ((n : ℤ) • a.1,(n : ℤ) * a.2)
def div (n : ℕ) (a : L) : L := (fun v => a.1 v / (n : ℤ), -((-a.2) / (n : ℤ)))

theorem item {{α : Type}} {{xs : List α}} {{x : α}} (i : ℕ) (eq : xs[i]? = some x) : x ∈ xs :=
  List.mem_iff_getElem?.mpr ⟨i,eq⟩

def p0 : List L := []

"""
    lines=[head]
    facts=["  have h0 : IsCPDerivation F p0 := .nil"]
    for i,ins in enumerate(derivation.ops):
        kind,*args=ins
        h=f"h{i}"
        at=lambda j: f"(item {i-1-j} rfl)"
        if kind=="row":
            p,=args; decl=f"clauseCP (row {p})"; proof=f".ax (row {p}) {h} (row_mem {p})"
        elif kind=="hole":
            p,q,t=args; decl=f"clauseCP (pair {p} {q} {t})";proof=f".ax (pair {p} {q} {t}) {h} (pair_mem {p} {q} {t} (by decide))"
        elif kind=="bool":
            p,t,s=args
            decl=f"(fun v => if v = ({p},{t}) then {1 if s==-1 else '(-1)'} else 0,{0 if s==-1 else '(-1)'})"
            proof=f".{'boolLo' if s==-1 else 'boolHi'} ({p},{t}) {h}"
        elif kind=="add":
            a,b=args;decl=f"add e{a} e{b}";proof=f".add {h} {at(a)} {at(b)}"
        else:
            n,a=args;decl=f"{kind} {n} e{a}";proof=f".{kind} {n} {h} {at(a)}"
            if kind=="div": proof+=" (by decide) (by decide +kernel)"
        lines.append(f"def e{i} : L := {decl}\ndef p{i+1} : List L := e{i} :: p{i}\n")
        facts.append(f"  have h{i+1} : IsCPDerivation F p{i+1} := {proof}")
    n=len(derivation.ops)
    lines.append(f"\ntheorem result : ∃ π : List L, IsCPRefutation F π ∧ π.length ≤ {n} := by")
    lines+=facts
    lines+= [f"  have last : e{n-1} = ((0 : V → ℤ), (1 : ℤ)) := by",
             "    apply Prod.ext", "    · exact funext (by decide +kernel)", "    · decide +kernel",
             f"  refine ⟨p{n},⟨h{n},?_⟩,by decide⟩", "  rw [← last]",
             "  exact List.Mem.head _", f"\nend {namespace}"]
    out.write_bytes(("\n".join(lines)+"\n").encode())


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--log",type=Path)
    p.add_argument("--out",type=Path,required=True)
    p.add_argument("--namespace",default="PigeonCP")
    a=p.parse_args()
    derivation=from_log(a.log) if a.log else regular()
    write_lean(derivation,a.out,a.namespace)
    print(len(derivation.ops),"lines",a.out)
