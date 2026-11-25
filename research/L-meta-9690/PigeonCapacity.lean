import PEqualNP.Defs

namespace PigeonCapacity
open PEqualNP.Search PEqualNP.ProofComplexity
abbrev V := Fin 5 × Fin 4
abbrev F := PHP 5 4
abbrev L := CPLine V

def row (i : Fin 5) : Clause V := Finset.univ.image (fun h : Fin 4 => ((i,h),true))
def pair (i j : Fin 5) (h : Fin 4) : Clause V := {((i,h),false),((j,h),false)}
theorem row_mem (i : Fin 5) : row i ∈ F := Or.inl ⟨i,rfl⟩
theorem pair_mem (i j : Fin 5) (h : Fin 4) (ne : i ≠ j) : pair i j h ∈ F :=
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

def e3 : L := clauseCP (pair 0 4 0)
def p4 : List L := e3 :: p3

def e4 : L := clauseCP (pair 1 2 0)
def p5 : List L := e4 :: p4

def e5 : L := clauseCP (pair 1 3 0)
def p6 : List L := e5 :: p5

def e6 : L := clauseCP (pair 1 4 0)
def p7 : List L := e6 :: p6

def e7 : L := clauseCP (pair 2 3 0)
def p8 : List L := e7 :: p7

def e8 : L := clauseCP (pair 2 4 0)
def p9 : List L := e8 :: p8

def e9 : L := clauseCP (pair 3 4 0)
def p10 : List L := e9 :: p9

def e10 : L := add e0 e1
def p11 : List L := e10 :: p10

def e11 : L := add e10 e4
def p12 : List L := e11 :: p11

def e12 : L := div 2 e11
def p13 : List L := e12 :: p12

def e13 : L := mul 2 e12
def p14 : List L := e13 :: p13

def e14 : L := add e13 e2
def p15 : List L := e14 :: p14

def e15 : L := add e14 e5
def p16 : List L := e15 :: p15

def e16 : L := add e15 e7
def p17 : List L := e16 :: p16

def e17 : L := div 3 e16
def p18 : List L := e17 :: p17

def e18 : L := mul 3 e17
def p19 : List L := e18 :: p18

def e19 : L := add e18 e3
def p20 : List L := e19 :: p19

def e20 : L := add e19 e6
def p21 : List L := e20 :: p20

def e21 : L := add e20 e8
def p22 : List L := e21 :: p21

def e22 : L := add e21 e9
def p23 : List L := e22 :: p22

def e23 : L := div 4 e22
def p24 : List L := e23 :: p23

def e24 : L := clauseCP (pair 0 1 1)
def p25 : List L := e24 :: p24

def e25 : L := clauseCP (pair 0 2 1)
def p26 : List L := e25 :: p25

def e26 : L := clauseCP (pair 0 3 1)
def p27 : List L := e26 :: p26

def e27 : L := clauseCP (pair 0 4 1)
def p28 : List L := e27 :: p27

def e28 : L := clauseCP (pair 1 2 1)
def p29 : List L := e28 :: p28

def e29 : L := clauseCP (pair 1 3 1)
def p30 : List L := e29 :: p29

def e30 : L := clauseCP (pair 1 4 1)
def p31 : List L := e30 :: p30

def e31 : L := clauseCP (pair 2 3 1)
def p32 : List L := e31 :: p31

def e32 : L := clauseCP (pair 2 4 1)
def p33 : List L := e32 :: p32

def e33 : L := clauseCP (pair 3 4 1)
def p34 : List L := e33 :: p33

def e34 : L := add e24 e25
def p35 : List L := e34 :: p34

def e35 : L := add e34 e28
def p36 : List L := e35 :: p35

def e36 : L := div 2 e35
def p37 : List L := e36 :: p36

def e37 : L := mul 2 e36
def p38 : List L := e37 :: p37

def e38 : L := add e37 e26
def p39 : List L := e38 :: p38

def e39 : L := add e38 e29
def p40 : List L := e39 :: p39

def e40 : L := add e39 e31
def p41 : List L := e40 :: p40

def e41 : L := div 3 e40
def p42 : List L := e41 :: p41

def e42 : L := mul 3 e41
def p43 : List L := e42 :: p42

def e43 : L := add e42 e27
def p44 : List L := e43 :: p43

def e44 : L := add e43 e30
def p45 : List L := e44 :: p44

def e45 : L := add e44 e32
def p46 : List L := e45 :: p45

def e46 : L := add e45 e33
def p47 : List L := e46 :: p46

def e47 : L := div 4 e46
def p48 : List L := e47 :: p47

def e48 : L := clauseCP (pair 0 1 2)
def p49 : List L := e48 :: p48

def e49 : L := clauseCP (pair 0 2 2)
def p50 : List L := e49 :: p49

def e50 : L := clauseCP (pair 0 3 2)
def p51 : List L := e50 :: p50

def e51 : L := clauseCP (pair 0 4 2)
def p52 : List L := e51 :: p51

def e52 : L := clauseCP (pair 1 2 2)
def p53 : List L := e52 :: p52

def e53 : L := clauseCP (pair 1 3 2)
def p54 : List L := e53 :: p53

def e54 : L := clauseCP (pair 1 4 2)
def p55 : List L := e54 :: p54

def e55 : L := clauseCP (pair 2 3 2)
def p56 : List L := e55 :: p55

def e56 : L := clauseCP (pair 2 4 2)
def p57 : List L := e56 :: p56

def e57 : L := clauseCP (pair 3 4 2)
def p58 : List L := e57 :: p57

def e58 : L := add e48 e49
def p59 : List L := e58 :: p58

def e59 : L := add e58 e52
def p60 : List L := e59 :: p59

def e60 : L := div 2 e59
def p61 : List L := e60 :: p60

def e61 : L := mul 2 e60
def p62 : List L := e61 :: p61

def e62 : L := add e61 e50
def p63 : List L := e62 :: p62

def e63 : L := add e62 e53
def p64 : List L := e63 :: p63

def e64 : L := add e63 e55
def p65 : List L := e64 :: p64

def e65 : L := div 3 e64
def p66 : List L := e65 :: p65

def e66 : L := mul 3 e65
def p67 : List L := e66 :: p66

def e67 : L := add e66 e51
def p68 : List L := e67 :: p67

def e68 : L := add e67 e54
def p69 : List L := e68 :: p68

def e69 : L := add e68 e56
def p70 : List L := e69 :: p69

def e70 : L := add e69 e57
def p71 : List L := e70 :: p70

def e71 : L := div 4 e70
def p72 : List L := e71 :: p71

def e72 : L := clauseCP (row 0)
def p73 : List L := e72 :: p72

def e73 : L := clauseCP (row 1)
def p74 : List L := e73 :: p73

def e74 : L := clauseCP (row 2)
def p75 : List L := e74 :: p74

def e75 : L := clauseCP (row 3)
def p76 : List L := e75 :: p75

def e76 : L := clauseCP (row 4)
def p77 : List L := e76 :: p76

def e77 : L := add e23 e47
def p78 : List L := e77 :: p77

def e78 : L := add e77 e71
def p79 : List L := e78 :: p78

def e79 : L := add e78 e72
def p80 : List L := e79 :: p79

def e80 : L := add e79 e73
def p81 : List L := e80 :: p80

def e81 : L := add e80 e74
def p82 : List L := e81 :: p81

def e82 : L := add e81 e75
def p83 : List L := e82 :: p82

def e83 : L := add e82 e76
def p84 : List L := e83 :: p83

def e84 : L := clauseCP (pair 0 1 3)
def p85 : List L := e84 :: p84

def e85 : L := clauseCP (pair 0 2 3)
def p86 : List L := e85 :: p85

def e86 : L := clauseCP (pair 0 3 3)
def p87 : List L := e86 :: p86

def e87 : L := clauseCP (pair 0 4 3)
def p88 : List L := e87 :: p87

def e88 : L := clauseCP (pair 1 2 3)
def p89 : List L := e88 :: p88

def e89 : L := clauseCP (pair 1 3 3)
def p90 : List L := e89 :: p89

def e90 : L := clauseCP (pair 1 4 3)
def p91 : List L := e90 :: p90

def e91 : L := clauseCP (pair 2 3 3)
def p92 : List L := e91 :: p91

def e92 : L := clauseCP (pair 2 4 3)
def p93 : List L := e92 :: p92

def e93 : L := clauseCP (pair 3 4 3)
def p94 : List L := e93 :: p93

def e94 : L := add e84 e85
def p95 : List L := e94 :: p94

def e95 : L := add e94 e88
def p96 : List L := e95 :: p95

def e96 : L := div 2 e95
def p97 : List L := e96 :: p96

def e97 : L := mul 2 e96
def p98 : List L := e97 :: p97

def e98 : L := add e97 e86
def p99 : List L := e98 :: p98

def e99 : L := add e98 e89
def p100 : List L := e99 :: p99

def e100 : L := add e99 e91
def p101 : List L := e100 :: p100

def e101 : L := div 3 e100
def p102 : List L := e101 :: p101

def e102 : L := mul 3 e101
def p103 : List L := e102 :: p102

def e103 : L := add e102 e87
def p104 : List L := e103 :: p103

def e104 : L := add e103 e90
def p105 : List L := e104 :: p104

def e105 : L := add e104 e92
def p106 : List L := e105 :: p105

def e106 : L := add e105 e93
def p107 : List L := e106 :: p106

def e107 : L := div 4 e106
def p108 : List L := e107 :: p107

def e108 : L := add e83 e107
def p109 : List L := e108 :: p108


theorem result : ∃ π : List L, IsCPRefutation F π ∧ π.length ≤ 109 := by
  have h0 : IsCPDerivation F p0 := .nil
  have h1 : IsCPDerivation F p1 := .ax (pair 0 1 0) h0 (pair_mem 0 1 0 (by decide))
  have h2 : IsCPDerivation F p2 := .ax (pair 0 2 0) h1 (pair_mem 0 2 0 (by decide))
  have h3 : IsCPDerivation F p3 := .ax (pair 0 3 0) h2 (pair_mem 0 3 0 (by decide))
  have h4 : IsCPDerivation F p4 := .ax (pair 0 4 0) h3 (pair_mem 0 4 0 (by decide))
  have h5 : IsCPDerivation F p5 := .ax (pair 1 2 0) h4 (pair_mem 1 2 0 (by decide))
  have h6 : IsCPDerivation F p6 := .ax (pair 1 3 0) h5 (pair_mem 1 3 0 (by decide))
  have h7 : IsCPDerivation F p7 := .ax (pair 1 4 0) h6 (pair_mem 1 4 0 (by decide))
  have h8 : IsCPDerivation F p8 := .ax (pair 2 3 0) h7 (pair_mem 2 3 0 (by decide))
  have h9 : IsCPDerivation F p9 := .ax (pair 2 4 0) h8 (pair_mem 2 4 0 (by decide))
  have h10 : IsCPDerivation F p10 := .ax (pair 3 4 0) h9 (pair_mem 3 4 0 (by decide))
  have h11 : IsCPDerivation F p11 := .add h10 (item 9 rfl) (item 8 rfl)
  have h12 : IsCPDerivation F p12 := .add h11 (item 0 rfl) (item 6 rfl)
  have h13 : IsCPDerivation F p13 := .div 2 h12 (item 0 rfl) (by decide) (by decide +kernel)
  have h14 : IsCPDerivation F p14 := .mul 2 h13 (item 0 rfl)
  have h15 : IsCPDerivation F p15 := .add h14 (item 0 rfl) (item 11 rfl)
  have h16 : IsCPDerivation F p16 := .add h15 (item 0 rfl) (item 9 rfl)
  have h17 : IsCPDerivation F p17 := .add h16 (item 0 rfl) (item 8 rfl)
  have h18 : IsCPDerivation F p18 := .div 3 h17 (item 0 rfl) (by decide) (by decide +kernel)
  have h19 : IsCPDerivation F p19 := .mul 3 h18 (item 0 rfl)
  have h20 : IsCPDerivation F p20 := .add h19 (item 0 rfl) (item 15 rfl)
  have h21 : IsCPDerivation F p21 := .add h20 (item 0 rfl) (item 13 rfl)
  have h22 : IsCPDerivation F p22 := .add h21 (item 0 rfl) (item 12 rfl)
  have h23 : IsCPDerivation F p23 := .add h22 (item 0 rfl) (item 12 rfl)
  have h24 : IsCPDerivation F p24 := .div 4 h23 (item 0 rfl) (by decide) (by decide +kernel)
  have h25 : IsCPDerivation F p25 := .ax (pair 0 1 1) h24 (pair_mem 0 1 1 (by decide))
  have h26 : IsCPDerivation F p26 := .ax (pair 0 2 1) h25 (pair_mem 0 2 1 (by decide))
  have h27 : IsCPDerivation F p27 := .ax (pair 0 3 1) h26 (pair_mem 0 3 1 (by decide))
  have h28 : IsCPDerivation F p28 := .ax (pair 0 4 1) h27 (pair_mem 0 4 1 (by decide))
  have h29 : IsCPDerivation F p29 := .ax (pair 1 2 1) h28 (pair_mem 1 2 1 (by decide))
  have h30 : IsCPDerivation F p30 := .ax (pair 1 3 1) h29 (pair_mem 1 3 1 (by decide))
  have h31 : IsCPDerivation F p31 := .ax (pair 1 4 1) h30 (pair_mem 1 4 1 (by decide))
  have h32 : IsCPDerivation F p32 := .ax (pair 2 3 1) h31 (pair_mem 2 3 1 (by decide))
  have h33 : IsCPDerivation F p33 := .ax (pair 2 4 1) h32 (pair_mem 2 4 1 (by decide))
  have h34 : IsCPDerivation F p34 := .ax (pair 3 4 1) h33 (pair_mem 3 4 1 (by decide))
  have h35 : IsCPDerivation F p35 := .add h34 (item 9 rfl) (item 8 rfl)
  have h36 : IsCPDerivation F p36 := .add h35 (item 0 rfl) (item 6 rfl)
  have h37 : IsCPDerivation F p37 := .div 2 h36 (item 0 rfl) (by decide) (by decide +kernel)
  have h38 : IsCPDerivation F p38 := .mul 2 h37 (item 0 rfl)
  have h39 : IsCPDerivation F p39 := .add h38 (item 0 rfl) (item 11 rfl)
  have h40 : IsCPDerivation F p40 := .add h39 (item 0 rfl) (item 9 rfl)
  have h41 : IsCPDerivation F p41 := .add h40 (item 0 rfl) (item 8 rfl)
  have h42 : IsCPDerivation F p42 := .div 3 h41 (item 0 rfl) (by decide) (by decide +kernel)
  have h43 : IsCPDerivation F p43 := .mul 3 h42 (item 0 rfl)
  have h44 : IsCPDerivation F p44 := .add h43 (item 0 rfl) (item 15 rfl)
  have h45 : IsCPDerivation F p45 := .add h44 (item 0 rfl) (item 13 rfl)
  have h46 : IsCPDerivation F p46 := .add h45 (item 0 rfl) (item 12 rfl)
  have h47 : IsCPDerivation F p47 := .add h46 (item 0 rfl) (item 12 rfl)
  have h48 : IsCPDerivation F p48 := .div 4 h47 (item 0 rfl) (by decide) (by decide +kernel)
  have h49 : IsCPDerivation F p49 := .ax (pair 0 1 2) h48 (pair_mem 0 1 2 (by decide))
  have h50 : IsCPDerivation F p50 := .ax (pair 0 2 2) h49 (pair_mem 0 2 2 (by decide))
  have h51 : IsCPDerivation F p51 := .ax (pair 0 3 2) h50 (pair_mem 0 3 2 (by decide))
  have h52 : IsCPDerivation F p52 := .ax (pair 0 4 2) h51 (pair_mem 0 4 2 (by decide))
  have h53 : IsCPDerivation F p53 := .ax (pair 1 2 2) h52 (pair_mem 1 2 2 (by decide))
  have h54 : IsCPDerivation F p54 := .ax (pair 1 3 2) h53 (pair_mem 1 3 2 (by decide))
  have h55 : IsCPDerivation F p55 := .ax (pair 1 4 2) h54 (pair_mem 1 4 2 (by decide))
  have h56 : IsCPDerivation F p56 := .ax (pair 2 3 2) h55 (pair_mem 2 3 2 (by decide))
  have h57 : IsCPDerivation F p57 := .ax (pair 2 4 2) h56 (pair_mem 2 4 2 (by decide))
  have h58 : IsCPDerivation F p58 := .ax (pair 3 4 2) h57 (pair_mem 3 4 2 (by decide))
  have h59 : IsCPDerivation F p59 := .add h58 (item 9 rfl) (item 8 rfl)
  have h60 : IsCPDerivation F p60 := .add h59 (item 0 rfl) (item 6 rfl)
  have h61 : IsCPDerivation F p61 := .div 2 h60 (item 0 rfl) (by decide) (by decide +kernel)
  have h62 : IsCPDerivation F p62 := .mul 2 h61 (item 0 rfl)
  have h63 : IsCPDerivation F p63 := .add h62 (item 0 rfl) (item 11 rfl)
  have h64 : IsCPDerivation F p64 := .add h63 (item 0 rfl) (item 9 rfl)
  have h65 : IsCPDerivation F p65 := .add h64 (item 0 rfl) (item 8 rfl)
  have h66 : IsCPDerivation F p66 := .div 3 h65 (item 0 rfl) (by decide) (by decide +kernel)
  have h67 : IsCPDerivation F p67 := .mul 3 h66 (item 0 rfl)
  have h68 : IsCPDerivation F p68 := .add h67 (item 0 rfl) (item 15 rfl)
  have h69 : IsCPDerivation F p69 := .add h68 (item 0 rfl) (item 13 rfl)
  have h70 : IsCPDerivation F p70 := .add h69 (item 0 rfl) (item 12 rfl)
  have h71 : IsCPDerivation F p71 := .add h70 (item 0 rfl) (item 12 rfl)
  have h72 : IsCPDerivation F p72 := .div 4 h71 (item 0 rfl) (by decide) (by decide +kernel)
  have h73 : IsCPDerivation F p73 := .ax (row 0) h72 (row_mem 0)
  have h74 : IsCPDerivation F p74 := .ax (row 1) h73 (row_mem 1)
  have h75 : IsCPDerivation F p75 := .ax (row 2) h74 (row_mem 2)
  have h76 : IsCPDerivation F p76 := .ax (row 3) h75 (row_mem 3)
  have h77 : IsCPDerivation F p77 := .ax (row 4) h76 (row_mem 4)
  have h78 : IsCPDerivation F p78 := .add h77 (item 53 rfl) (item 29 rfl)
  have h79 : IsCPDerivation F p79 := .add h78 (item 0 rfl) (item 6 rfl)
  have h80 : IsCPDerivation F p80 := .add h79 (item 0 rfl) (item 6 rfl)
  have h81 : IsCPDerivation F p81 := .add h80 (item 0 rfl) (item 6 rfl)
  have h82 : IsCPDerivation F p82 := .add h81 (item 0 rfl) (item 6 rfl)
  have h83 : IsCPDerivation F p83 := .add h82 (item 0 rfl) (item 6 rfl)
  have h84 : IsCPDerivation F p84 := .add h83 (item 0 rfl) (item 6 rfl)
  have h85 : IsCPDerivation F p85 := .ax (pair 0 1 3) h84 (pair_mem 0 1 3 (by decide))
  have h86 : IsCPDerivation F p86 := .ax (pair 0 2 3) h85 (pair_mem 0 2 3 (by decide))
  have h87 : IsCPDerivation F p87 := .ax (pair 0 3 3) h86 (pair_mem 0 3 3 (by decide))
  have h88 : IsCPDerivation F p88 := .ax (pair 0 4 3) h87 (pair_mem 0 4 3 (by decide))
  have h89 : IsCPDerivation F p89 := .ax (pair 1 2 3) h88 (pair_mem 1 2 3 (by decide))
  have h90 : IsCPDerivation F p90 := .ax (pair 1 3 3) h89 (pair_mem 1 3 3 (by decide))
  have h91 : IsCPDerivation F p91 := .ax (pair 1 4 3) h90 (pair_mem 1 4 3 (by decide))
  have h92 : IsCPDerivation F p92 := .ax (pair 2 3 3) h91 (pair_mem 2 3 3 (by decide))
  have h93 : IsCPDerivation F p93 := .ax (pair 2 4 3) h92 (pair_mem 2 4 3 (by decide))
  have h94 : IsCPDerivation F p94 := .ax (pair 3 4 3) h93 (pair_mem 3 4 3 (by decide))
  have h95 : IsCPDerivation F p95 := .add h94 (item 9 rfl) (item 8 rfl)
  have h96 : IsCPDerivation F p96 := .add h95 (item 0 rfl) (item 6 rfl)
  have h97 : IsCPDerivation F p97 := .div 2 h96 (item 0 rfl) (by decide) (by decide +kernel)
  have h98 : IsCPDerivation F p98 := .mul 2 h97 (item 0 rfl)
  have h99 : IsCPDerivation F p99 := .add h98 (item 0 rfl) (item 11 rfl)
  have h100 : IsCPDerivation F p100 := .add h99 (item 0 rfl) (item 9 rfl)
  have h101 : IsCPDerivation F p101 := .add h100 (item 0 rfl) (item 8 rfl)
  have h102 : IsCPDerivation F p102 := .div 3 h101 (item 0 rfl) (by decide) (by decide +kernel)
  have h103 : IsCPDerivation F p103 := .mul 3 h102 (item 0 rfl)
  have h104 : IsCPDerivation F p104 := .add h103 (item 0 rfl) (item 15 rfl)
  have h105 : IsCPDerivation F p105 := .add h104 (item 0 rfl) (item 13 rfl)
  have h106 : IsCPDerivation F p106 := .add h105 (item 0 rfl) (item 12 rfl)
  have h107 : IsCPDerivation F p107 := .add h106 (item 0 rfl) (item 12 rfl)
  have h108 : IsCPDerivation F p108 := .div 4 h107 (item 0 rfl) (by decide) (by decide +kernel)
  have h109 : IsCPDerivation F p109 := .add h108 (item 24 rfl) (item 0 rfl)
  have last : e108 = ((0 : V → ℤ), (1 : ℤ)) := by
    apply Prod.ext
    · exact funext (by decide +kernel)
    · decide +kernel
  refine ⟨p109,⟨h109,?_⟩,by decide⟩
  rw [← last]
  exact List.Mem.head _

end PigeonCapacity
