import Plane4Transport

namespace Plane4Tests
open SmallAnd PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def edgeSpec (x : V → Bool) : Prop := ∃ u v : V, (u.val < 21 ∧ 21 ≤ v.val ∧
    (v.val+21-u.val)%21 ∈ ([0,5,7,17,20] : List Nat)) ∧ x u = true ∧ x v = true

theorem exactFlag (u v : V) : flag u v = true ↔ u.val < 21 ∧ 21 ≤ v.val ∧
    (v.val+21-u.val)%21 ∈ ([0,5,7,17,20] : List Nat) := by
  simp only [flag,Bool.and_eq_true,decide_eq_true_eq,List.contains_iff_mem,and_assoc]

theorem edge_spec (x : V → Bool) : Positive x ↔ edgeSpec x := by
  constructor
  · rintro ⟨u,v,yes,hu,hv⟩
    rcases Bool.or_eq_true_iff.mp yes with e | e
    · exact ⟨u,v,(exactFlag u v).mp e,hu,hv⟩
    · exact ⟨v,u,(exactFlag v u).mp e,hv,hu⟩
  · rintro ⟨u,v,e,hu,hv⟩
    exact ⟨u,v,Bool.or_eq_true_iff.mpr (Or.inl ((exactFlag u v).mpr e)),hu,hv⟩

def seedInput (v : V) : Bool := decide (v.val ∈ ([0,1,2,6,8,18,24,31,33,37] : List Nat))
theorem seed_input : (fun v : V => decide (v ∈ seedSet)) = seedInput := by
  funext v
  simp [seedSet,seedInput,seed]
def seedHit (C : Circuit) : Prop := ∃ j g, C.gates[j]? = some g ∧ g.op = .and ∧
  (C.wires (List.ofFn seedInput)).getD (42+j) false = true
theorem seed_hit (C : Circuit) : Active C.gates seedSet ↔ seedHit C := by
  simp only [Active,wire,values,seed_input,seedHit,Circuit.wires]

def Posted : Prop := ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → (∃ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x4]? = Option.some x5 ∧ x5.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x6 : Fin (42 : ℕ)) => Decidable.decide (↑x6 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)]))).getD ((42 : ℕ) + x4) Bool.false = Bool.true) → ∃ (x5 : Fin (42 : ℕ) → Bool), ¬(x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), (↑x6 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x7 ∧ (↑x7 + (21 : ℕ) - ↑x6) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true)

theorem posted_equivalent : Posted ↔ ¬ ∃ C : Circuit, C.size ≤ 124 ∧ Monotone2 C ∧ Correct C ∧
    ∃ S, Negative S ∧ Active C.gates S := by
  classical
  rw [dirty_equivalence]
  change (∀ C : Circuit, Monotone2 C → C.size ≤ 124 → seedHit C →
    ∃ x : V → Bool, ¬ (C.eval (List.ofFn x) = true ↔ edgeSpec x)) ↔ _
  constructor
  · rintro all ⟨C,bd,m,c,a⟩
    obtain ⟨x,h⟩ := all C m bd ((seed_hit C).mp a)
    exact h ((c x).trans (edge_spec x))
  · intro none C m bd a
    by_contra bad
    push Not at bad
    exact none ⟨C,bd,m,fun x => (bad x).trans (edge_spec x).symm,(seed_hit C).mpr a⟩

end Plane4Tests
