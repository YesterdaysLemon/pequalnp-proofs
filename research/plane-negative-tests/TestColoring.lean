import SmallAnd

namespace TestColoring
open SmallAnd PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {V : Type} [DecidableEq V]
def Free (edge : V → V → Prop) (S : Finset V) : Prop := ∀ u ∈ S, ∀ v ∈ S, ¬edge u v
abbrev Demand (edge : V → V → Prop) := {S : Finset V // S.card ≤ 2 ∧ Free edge S}
def Suite (edge : V → V → Prop) (k : Nat) : Prop := ∃ tests : Fin k → Finset V,
  (∀ i, Free edge (tests i)) ∧ ∀ d : Demand edge, ∃ i, d.val ⊆ tests i
def Coloring (edge : V → V → Prop) (k : Nat) : Prop := ∃ color : Demand edge → Fin k,
  ∀ a b, color a=color b → Free edge (a.val ∪ b.val)

theorem free_down (edge : V → V → Prop) {A B : Finset V} (free : Free edge B) (sub : A ⊆ B) : Free edge A :=
  fun p hp q hq => free p (sub hp) q (sub hq)

theorem suite_coloring [Fintype V] (edge : V → V → Prop) (k : Nat) : Suite edge k ↔ Coloring edge k := by
  classical
  constructor
  · rintro ⟨tests,free,cover⟩
    choose color belongs using cover
    refine ⟨color,fun a b eq => free_down edge (free (color b)) (Finset.union_subset ?_ (belongs b))⟩
    simpa [←eq] using belongs a
  · rintro ⟨color,h⟩
    let tests (i : Fin k) := (Finset.univ.filter fun d : Demand edge => color d=i).biUnion fun d => d.val
    refine ⟨tests,?_,?_⟩
    · intro i u hu v hv
      obtain ⟨a,ha,au⟩ := Finset.mem_biUnion.mp hu
      obtain ⟨b,hb,bv⟩ := Finset.mem_biUnion.mp hv
      have eq := (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
      exact h a b eq u (Finset.mem_union_left _ au) v (Finset.mem_union_right _ bv)
    · intro d
      exact ⟨color d,fun u hu => Finset.mem_biUnion.mpr ⟨d,by simp,hu⟩⟩

theorem detection_coloring {n : Nat} (edge : Fin n → Fin n → Prop) (k : Nat) :
    (∃ tests : Fin k → Finset (Fin n), (∀ i, Free edge (tests i)) ∧
      ∀ C : Circuit, Monotone2 C →
      ((∃ S, Free edge S ∧ Active C.gates S) ↔ ∃ i, Active C.gates (tests i))) ↔ Coloring edge k := by
  classical
  rw [← suite_coloring]
  constructor
  · rintro ⟨tests,free,detect⟩
    refine ⟨tests,free,?_⟩
    intro d
    obtain ⟨i,act⟩ := (detect (probe d.val) (probe_small d.val d.property.1)).mp
      ⟨d.val,d.property.2,(probe_active d.val d.val).mpr (by rfl)⟩
    exact ⟨i,(probe_active _ _).mp act⟩
  · rintro ⟨tests,free,cover⟩
    refine ⟨tests,free,fun C mono => ⟨?_,?_⟩⟩
    · rintro ⟨S,h,act⟩
      obtain ⟨T,sub,bd,yes⟩ := sparse C mono S act
      obtain ⟨i,ext⟩ := cover ⟨T,bd,free_down edge h sub⟩
      exact ⟨i,mono_active C mono ext yes⟩
    · rintro ⟨i,act⟩
      exact ⟨tests i,free i,act⟩

end TestColoring
