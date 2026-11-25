import PEqualNP.Defs

namespace Graph10760
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def edges : List (ℕ × ℕ) := [(0,2),(1,3),(0,4),(1,4),(2,4),(0,5),(1,5),(3,5),(0,6),(2,6),(3,6),(5,6)]
def hasEdge (bits : List Bool) : Bool :=
  edges.any (fun p => bits.getD p.1 false && bits.getD p.2 false)

def binary (g : Gate) : Bool := match g.op with
  | .and | .or => true
  | _ => false
def usable (g : Gate) : Bool := binary g && decide (g.inputs.length ≤ 2)

theorem binary_true (g : Gate) : binary g = true ↔ (g.op = GateOp.and ∨ g.op = GateOp.or) := by
  obtain ⟨op,args⟩ := g
  cases op <;> simp [binary]

theorem monotoneOfTest (c : Circuit) (h : c.gates.all usable = true) : Monotone2 c := by
  intro g hg
  have test := List.all_eq_true.mp h g hg
  simp only [usable,Bool.and_eq_true,decide_eq_true_eq] at test
  exact ⟨(binary_true g).mp test.1,test.2⟩

def whole : Circuit := ⟨[⟨.or,[0,2]⟩,⟨.or,[2,5]⟩,⟨.or,[3,5]⟩,⟨.or,[4,6]⟩,⟨.or,[4,9]⟩,⟨.and,[0,8]⟩,⟨.and,[1,11]⟩,⟨.and,[7,10]⟩,⟨.and,[3,5]⟩,⟨.and,[9,6]⟩,⟨.or,[12,13]⟩,⟨.or,[14,15]⟩,⟨.or,[17,18]⟩,⟨.or,[19,16]⟩],20⟩

theorem upper : Monotone2 whole ∧ whole.size = 14 ∧
    ∀ x : Fin 7 → Bool, whole.eval (List.ofFn x) = hasEdge (List.ofFn x) := by
  exact ⟨monotoneOfTest whole (by decide +kernel),rfl,by decide +kernel⟩

def deletion : Fin 7 → Circuit
  | 0 => ⟨[⟨.or,[0,1]⟩,⟨.or,[0,5]⟩,⟨.and,[1,5]⟩,⟨.and,[2,4]⟩,⟨.or,[2,4]⟩,⟨.and,[3,6]⟩,⟨.or,[7,9]⟩,⟨.or,[8,10]⟩,⟨.and,[12,13]⟩,⟨.or,[11,14]⟩],15⟩
  | 1 => ⟨[⟨.or,[0,1]⟩,⟨.or,[0,2]⟩,⟨.or,[0,5]⟩,⟨.or,[1,4]⟩,⟨.and,[3,6]⟩,⟨.or,[4,5]⟩,⟨.and,[7,11]⟩,⟨.and,[8,9]⟩,⟨.or,[10,12]⟩,⟨.or,[13,14]⟩],15⟩
  | 2 => ⟨[⟨.or,[0,1]⟩,⟨.or,[0,2]⟩,⟨.or,[1,4]⟩,⟨.and,[2,8]⟩,⟨.or,[3,4]⟩,⟨.or,[4,7]⟩,⟨.or,[5,9]⟩,⟨.and,[6,10]⟩,⟨.and,[11,12]⟩,⟨.or,[13,14]⟩],15⟩
  | 3 => ⟨[⟨.or,[0,1]⟩,⟨.or,[0,2]⟩,⟨.or,[0,3]⟩,⟨.and,[2,8]⟩,⟨.or,[3,4]⟩,⟨.or,[4,7]⟩,⟨.or,[5,9]⟩,⟨.and,[6,10]⟩,⟨.and,[11,12]⟩,⟨.or,[13,14]⟩],15⟩
  | 4 => ⟨[⟨.or,[0,3]⟩,⟨.or,[0,5]⟩,⟨.or,[1,5]⟩,⟨.and,[2,7]⟩,⟨.or,[3,4]⟩,⟨.or,[4,5]⟩,⟨.and,[6,11]⟩,⟨.and,[8,10]⟩,⟨.or,[9,12]⟩,⟨.or,[13,14]⟩],15⟩
  | 5 => ⟨[⟨.and,[0,2]⟩,⟨.or,[0,2]⟩,⟨.and,[1,3]⟩,⟨.or,[1,7]⟩,⟨.or,[3,7]⟩,⟨.or,[4,6]⟩,⟨.or,[5,8]⟩,⟨.and,[9,11]⟩,⟨.and,[10,12]⟩,⟨.or,[13,14]⟩],15⟩
  | _ => ⟨[⟨.or,[0,1]⟩,⟨.or,[0,4]⟩,⟨.or,[1,5]⟩,⟨.and,[2,7]⟩,⟨.and,[3,8]⟩,⟨.or,[4,5]⟩,⟨.and,[6,11]⟩,⟨.or,[9,10]⟩,⟨.or,[12,13]⟩],14⟩

theorem deletionUpper (v : Fin 7) : Monotone2 (deletion v) ∧
    (deletion v).size = (if v.val = 6 then 9 else 10) ∧
    ∀ x : Fin 6 → Bool, (deletion v).eval (List.ofFn x) =
      hasEdge ((List.ofFn x).insertIdx v.val false) := by
  have checks : ∀ i : Fin 7, (deletion i).gates.all usable = true ∧
      (deletion i).size = (if i.val = 6 then 9 else 10) ∧
      ∀ x : Fin 6 → Bool, (deletion i).eval (List.ofFn x) =
        hasEdge ((List.ofFn x).insertIdx i.val false) := by decide +kernel
  exact ⟨monotoneOfTest _ (checks v).1,(checks v).2⟩

/-- The independent signed search establishes the numerical premise of this implication. -/
theorem replacementFromBinaryBound
    (bound : ∀ c : Circuit,
      (∀ g ∈ c.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
      (∀ x : Fin 7 → Bool, c.eval (List.ofFn x) = hasEdge (List.ofFn x)) →
      13 ≤ (c.gates.filter binary).length)
    (c : Circuit)
    (legal : ∀ g ∈ c.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (computes : ∀ x : Fin 7 → Bool, c.eval (List.ofFn x) = hasEdge (List.ofFn x)) :
    ∃ d : Circuit, Monotone2 d ∧ d.size ≤ c.size ∧
      ∀ x : Fin 7 → Bool, d.eval (List.ofFn x) = hasEdge (List.ofFn x) := by
  by_cases h : ∃ g ∈ c.gates, g.op = GateOp.not
  · obtain ⟨g,hg,neg⟩ := h
    have strict : (c.gates.filter binary).length < c.gates.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨g,hg,by simp [binary,neg]⟩
    have lower := bound c legal computes
    refine ⟨whole,upper.1,?_,upper.2.2⟩
    rw [upper.2.1]
    change 14 ≤ c.gates.length
    omega
  · refine ⟨c,?_,le_rfl,computes⟩
    intro g hg
    rcases legal g hg with ⟨ha|hb|hc,sz⟩
    · exact ⟨Or.inl ha,sz⟩
    · exact ⟨Or.inr hb,sz⟩
    · exact (h ⟨g,hg,hc⟩).elim

end Graph10760
