import PEqualNP.Defs

namespace PigeonCP
open PEqualNP.Search PEqualNP.ProofComplexity
abbrev V := Fin 4 × Fin 3
abbrev F := PHP 4 3
abbrev L := CPLine V

def row (i : Fin 4) : Clause V := Finset.univ.image (fun h : Fin 3 => ((i,h),true))
def pair (i j : Fin 4) (h : Fin 3) : Clause V := {((i,h),false),((j,h),false)}
theorem row_mem (i : Fin 4) : row i ∈ F := Or.inl ⟨i,rfl⟩
theorem pair_mem (i j : Fin 4) (h : Fin 3) (ne : i ≠ j) : pair i j h ∈ F :=
  Or.inr ⟨i,j,h,ne,rfl⟩

def add (a b : L) : L := (a.1 + b.1,a.2 + b.2)
def mul (n : ℕ) (a : L) : L := ((n : ℤ) • a.1,(n : ℤ) * a.2)
def div (n : ℕ) (a : L) : L := (fun v => a.1 v / (n : ℤ), -((-a.2) / (n : ℤ)))

theorem item {α : Type} {xs : List α} {x : α} (i : ℕ) (eq : xs[i]? = some x) : x ∈ xs :=
  List.mem_iff_getElem?.mpr ⟨i,eq⟩

def p0 : List L := []


def e0 : L := clauseCP (pair 0 1 0)
def p1 : List L := e0 :: p0

def e1 : L := clauseCP (pair 0 2 0)
def p2 : List L := e1 :: p1

def e2 : L := clauseCP (pair 0 3 0)
def p3 : List L := e2 :: p2

def e3 : L := clauseCP (pair 1 2 0)
def p4 : List L := e3 :: p3

def e4 : L := clauseCP (pair 1 3 0)
def p5 : List L := e4 :: p4

def e5 : L := clauseCP (pair 2 3 0)
def p6 : List L := e5 :: p5

def e6 : L := add e0 e1
def p7 : List L := e6 :: p6

def e7 : L := add e6 e3
def p8 : List L := e7 :: p7

def e8 : L := div 2 e7
def p9 : List L := e8 :: p8

def e9 : L := mul 2 e8
def p10 : List L := e9 :: p9

def e10 : L := add e9 e2
def p11 : List L := e10 :: p10

def e11 : L := add e10 e4
def p12 : List L := e11 :: p11

def e12 : L := add e11 e5
def p13 : List L := e12 :: p12

def e13 : L := div 3 e12
def p14 : List L := e13 :: p13

def e14 : L := clauseCP (pair 0 1 1)
def p15 : List L := e14 :: p14

def e15 : L := clauseCP (pair 0 2 1)
def p16 : List L := e15 :: p15

def e16 : L := clauseCP (pair 0 3 1)
def p17 : List L := e16 :: p16

def e17 : L := clauseCP (pair 1 2 1)
def p18 : List L := e17 :: p17

def e18 : L := clauseCP (pair 1 3 1)
def p19 : List L := e18 :: p18

def e19 : L := clauseCP (pair 2 3 1)
def p20 : List L := e19 :: p19

def e20 : L := add e14 e15
def p21 : List L := e20 :: p20

def e21 : L := add e20 e17
def p22 : List L := e21 :: p21

def e22 : L := div 2 e21
def p23 : List L := e22 :: p22

def e23 : L := mul 2 e22
def p24 : List L := e23 :: p23

def e24 : L := add e23 e16
def p25 : List L := e24 :: p24

def e25 : L := add e24 e18
def p26 : List L := e25 :: p25

def e26 : L := add e25 e19
def p27 : List L := e26 :: p26

def e27 : L := div 3 e26
def p28 : List L := e27 :: p27

def e28 : L := clauseCP (pair 0 1 2)
def p29 : List L := e28 :: p28

def e29 : L := clauseCP (pair 0 2 2)
def p30 : List L := e29 :: p29

def e30 : L := clauseCP (pair 0 3 2)
def p31 : List L := e30 :: p30

def e31 : L := clauseCP (pair 1 2 2)
def p32 : List L := e31 :: p31

def e32 : L := clauseCP (pair 1 3 2)
def p33 : List L := e32 :: p32

def e33 : L := clauseCP (pair 2 3 2)
def p34 : List L := e33 :: p33

def e34 : L := add e28 e29
def p35 : List L := e34 :: p34

def e35 : L := add e34 e31
def p36 : List L := e35 :: p35

def e36 : L := div 2 e35
def p37 : List L := e36 :: p36

def e37 : L := mul 2 e36
def p38 : List L := e37 :: p37

def e38 : L := add e37 e30
def p39 : List L := e38 :: p38

def e39 : L := add e38 e32
def p40 : List L := e39 :: p39

def e40 : L := add e39 e33
def p41 : List L := e40 :: p40

def e41 : L := div 3 e40
def p42 : List L := e41 :: p41

def e42 : L := clauseCP (row 0)
def p43 : List L := e42 :: p42

def e43 : L := clauseCP (row 1)
def p44 : List L := e43 :: p43

def e44 : L := clauseCP (row 2)
def p45 : List L := e44 :: p44

def e45 : L := clauseCP (row 3)
def p46 : List L := e45 :: p45

def e46 : L := add e13 e27
def p47 : List L := e46 :: p46

def e47 : L := add e46 e41
def p48 : List L := e47 :: p47

def e48 : L := add e47 e42
def p49 : List L := e48 :: p48

def e49 : L := add e48 e43
def p50 : List L := e49 :: p49

def e50 : L := add e49 e44
def p51 : List L := e50 :: p50

def e51 : L := add e50 e45
def p52 : List L := e51 :: p51


theorem result : ∃ π : List L, IsCPRefutation F π ∧ π.length ≤ 52 := by
  have h0 : IsCPDerivation F p0 := .nil
  have h1 : IsCPDerivation F p1 := .ax (pair 0 1 0) h0 (pair_mem 0 1 0 (by decide))
  have h2 : IsCPDerivation F p2 := .ax (pair 0 2 0) h1 (pair_mem 0 2 0 (by decide))
  have h3 : IsCPDerivation F p3 := .ax (pair 0 3 0) h2 (pair_mem 0 3 0 (by decide))
  have h4 : IsCPDerivation F p4 := .ax (pair 1 2 0) h3 (pair_mem 1 2 0 (by decide))
  have h5 : IsCPDerivation F p5 := .ax (pair 1 3 0) h4 (pair_mem 1 3 0 (by decide))
  have h6 : IsCPDerivation F p6 := .ax (pair 2 3 0) h5 (pair_mem 2 3 0 (by decide))
  have h7 : IsCPDerivation F p7 := .add h6 (item 5 rfl) (item 4 rfl)
  have h8 : IsCPDerivation F p8 := .add h7 (item 0 rfl) (item 3 rfl)
  have h9 : IsCPDerivation F p9 := .div 2 h8 (item 0 rfl) (by decide) (by decide +kernel)
  have h10 : IsCPDerivation F p10 := .mul 2 h9 (item 0 rfl)
  have h11 : IsCPDerivation F p11 := .add h10 (item 0 rfl) (item 7 rfl)
  have h12 : IsCPDerivation F p12 := .add h11 (item 0 rfl) (item 6 rfl)
  have h13 : IsCPDerivation F p13 := .add h12 (item 0 rfl) (item 6 rfl)
  have h14 : IsCPDerivation F p14 := .div 3 h13 (item 0 rfl) (by decide) (by decide +kernel)
  have h15 : IsCPDerivation F p15 := .ax (pair 0 1 1) h14 (pair_mem 0 1 1 (by decide))
  have h16 : IsCPDerivation F p16 := .ax (pair 0 2 1) h15 (pair_mem 0 2 1 (by decide))
  have h17 : IsCPDerivation F p17 := .ax (pair 0 3 1) h16 (pair_mem 0 3 1 (by decide))
  have h18 : IsCPDerivation F p18 := .ax (pair 1 2 1) h17 (pair_mem 1 2 1 (by decide))
  have h19 : IsCPDerivation F p19 := .ax (pair 1 3 1) h18 (pair_mem 1 3 1 (by decide))
  have h20 : IsCPDerivation F p20 := .ax (pair 2 3 1) h19 (pair_mem 2 3 1 (by decide))
  have h21 : IsCPDerivation F p21 := .add h20 (item 5 rfl) (item 4 rfl)
  have h22 : IsCPDerivation F p22 := .add h21 (item 0 rfl) (item 3 rfl)
  have h23 : IsCPDerivation F p23 := .div 2 h22 (item 0 rfl) (by decide) (by decide +kernel)
  have h24 : IsCPDerivation F p24 := .mul 2 h23 (item 0 rfl)
  have h25 : IsCPDerivation F p25 := .add h24 (item 0 rfl) (item 7 rfl)
  have h26 : IsCPDerivation F p26 := .add h25 (item 0 rfl) (item 6 rfl)
  have h27 : IsCPDerivation F p27 := .add h26 (item 0 rfl) (item 6 rfl)
  have h28 : IsCPDerivation F p28 := .div 3 h27 (item 0 rfl) (by decide) (by decide +kernel)
  have h29 : IsCPDerivation F p29 := .ax (pair 0 1 2) h28 (pair_mem 0 1 2 (by decide))
  have h30 : IsCPDerivation F p30 := .ax (pair 0 2 2) h29 (pair_mem 0 2 2 (by decide))
  have h31 : IsCPDerivation F p31 := .ax (pair 0 3 2) h30 (pair_mem 0 3 2 (by decide))
  have h32 : IsCPDerivation F p32 := .ax (pair 1 2 2) h31 (pair_mem 1 2 2 (by decide))
  have h33 : IsCPDerivation F p33 := .ax (pair 1 3 2) h32 (pair_mem 1 3 2 (by decide))
  have h34 : IsCPDerivation F p34 := .ax (pair 2 3 2) h33 (pair_mem 2 3 2 (by decide))
  have h35 : IsCPDerivation F p35 := .add h34 (item 5 rfl) (item 4 rfl)
  have h36 : IsCPDerivation F p36 := .add h35 (item 0 rfl) (item 3 rfl)
  have h37 : IsCPDerivation F p37 := .div 2 h36 (item 0 rfl) (by decide) (by decide +kernel)
  have h38 : IsCPDerivation F p38 := .mul 2 h37 (item 0 rfl)
  have h39 : IsCPDerivation F p39 := .add h38 (item 0 rfl) (item 7 rfl)
  have h40 : IsCPDerivation F p40 := .add h39 (item 0 rfl) (item 6 rfl)
  have h41 : IsCPDerivation F p41 := .add h40 (item 0 rfl) (item 6 rfl)
  have h42 : IsCPDerivation F p42 := .div 3 h41 (item 0 rfl) (by decide) (by decide +kernel)
  have h43 : IsCPDerivation F p43 := .ax (row 0) h42 (row_mem 0)
  have h44 : IsCPDerivation F p44 := .ax (row 1) h43 (row_mem 1)
  have h45 : IsCPDerivation F p45 := .ax (row 2) h44 (row_mem 2)
  have h46 : IsCPDerivation F p46 := .ax (row 3) h45 (row_mem 3)
  have h47 : IsCPDerivation F p47 := .add h46 (item 32 rfl) (item 18 rfl)
  have h48 : IsCPDerivation F p48 := .add h47 (item 0 rfl) (item 5 rfl)
  have h49 : IsCPDerivation F p49 := .add h48 (item 0 rfl) (item 5 rfl)
  have h50 : IsCPDerivation F p50 := .add h49 (item 0 rfl) (item 5 rfl)
  have h51 : IsCPDerivation F p51 := .add h50 (item 0 rfl) (item 5 rfl)
  have h52 : IsCPDerivation F p52 := .add h51 (item 0 rfl) (item 5 rfl)
  have last : e51 = ((0 : V → ℤ), (1 : ℤ)) := by
    apply Prod.ext
    · exact funext (by decide +kernel)
    · decide +kernel
  refine ⟨p52,⟨h52,?_⟩,by decide⟩
  rw [← last]
  exact List.Mem.head _

end PigeonCP
