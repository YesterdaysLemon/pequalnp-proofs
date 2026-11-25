import CycleLifting
import PEqualNP.MetaComplexity.Helpers.PermInputs
import PEqualNP.MetaComplexity.Helpers.CoverCircuitList

namespace PuncturedPlane

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def es : List (ℕ × ℕ) := [(0,26),(0,28),(0,38),(0,41),(1,21),(1,22),(1,27),(1,29),(1,39),(2,22),(2,23),(2,28),(2,30),(2,40),(3,23),(3,24),(3,29),(3,31),(3,41),(4,21),(4,24),(4,25),(4,30),(4,32),(5,22),(5,25),(5,26),(5,31),(5,33),(6,23),(6,26),(6,27),(6,32),(6,34),(7,24),(7,27),(7,28),(7,33),(7,35),(8,25),(8,28),(8,29),(8,34),(8,36),(9,26),(9,29),(9,30),(9,35),(9,37),(10,27),(10,30),(10,31),(10,36),(10,38),(11,28),(11,31),(11,32),(11,37),(11,39),(12,29),(12,32),(12,33),(12,38),(12,40),(13,30),(13,33),(13,34),(13,39),(13,41),(14,21),(14,31),(14,34),(14,35),(14,40),(15,22),(15,32),(15,35),(15,36),(15,41),(16,21),(16,23),(16,33),(16,36),(16,37),(17,22),(17,24),(17,34),(17,37),(17,38),(18,23),(18,25),(18,35),(18,38),(18,39),(19,24),(19,26),(19,36),(19,39),(19,40),(20,25),(20,27),(20,37),(20,40),(20,41)]
def old (i : Fin 42) : Fin 42 := (![0,26,5,22,2,23,3,24,4,21,14,34,13,39,11,37,20,27,10,38,1,6,7,8,9,12,15,16,17,18,19,25,28,29,30,31,32,33,35,36,40,41] : Fin 42 → Fin 42) i
def newIndex (i : Fin 42) : Fin 42 := (![0,20,4,6,8,2,21,22,23,24,18,14,25,12,10,26,27,28,29,30,16,9,3,5,7,31,1,17,32,33,34,35,36,37,11,38,39,15,19,13,40,41] : Fin 42 → Fin 42) i
theorem old_new : ∀ i, old (newIndex i) = i := by decide +kernel
theorem new_old : ∀ i, newIndex (old i) = i := by decide +kernel
def rel (i j : Fin 42) : Prop := ((old i).val,(old j).val) ∈ es ∨ ((old j).val,(old i).val) ∈ es
instance (i j : Fin 42) : Decidable (rel i j) := inferInstanceAs (Decidable (_ ∨ _))
def G : SimpleGraph (Fin 42) where
  Adj := rel
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨by decide +kernel⟩
instance : DecidableRel G.Adj := fun i j => inferInstanceAs (Decidable (rel i j))
def target (x : Fin 42 → Bool) : Bool :=
  decide (∃ u v : Fin 42, (u.val,v.val) ∈ es ∧ x u = true ∧ x v = true)

theorem identify (x : Fin 42 → Bool) : target (x ∘ newIndex) = CycleLifting.graphFun G x := by
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨u,v,h,hu,hv⟩
    refine ⟨newIndex u,newIndex v,?_,hu,hv⟩
    exact Or.inl (by simpa only [old_new] using h)
  · rintro ⟨u,v,h,hu,hv⟩
    rcases h with forward | back
    · exact ⟨old u,old v,forward,by simpa [Function.comp_apply,new_old] using hu,
        by simpa [Function.comp_apply,new_old] using hv⟩
    · exact ⟨old v,old u,back,by simpa [Function.comp_apply,new_old] using hv,
        by simpa [Function.comp_apply,new_old] using hu⟩

set_option maxHeartbeats 0 in
theorem lower (s : ℕ) (h : HasCircuitSize 42 target s) : 51 ≤ s := by
  have permuted := Helpers.PermInputs.relabel_size newIndex target s h
  simp only [identify] at permuted
  have core : ∀ i j : Fin 20, G.Adj (Fin.castLE (by decide : 20 ≤ 42) i) (Fin.castLE (by decide) j) ↔
      (i.val+1)%20 = j.val ∨ (j.val+1)%20 = i.val := by decide +kernel
  have attach : ∀ v : Fin 42, 20 ≤ v.val → ∃ w : Fin 42, w.val < v.val ∧ G.Adj v w := by decide +kernel
  have count := CycleLifting.onGraph (by decide : 5 ≤ 20) (by decide : 20 ≤ 42) G core attach permuted
  omega

theorem onCircuit (C : Circuit) (fan : FanInTwo C)
    (correct : ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 42, (u.val,v.val) ∈ es ∧ x u = true ∧ x v = true) : 51 ≤ C.size := by
  apply lower C.size
  refine ⟨C,fan,le_rfl,?_⟩
  intro x
  apply Bool.eq_iff_iff.mpr
  simpa only [target,decide_eq_true_eq] using correct x

def witness : Circuit := CoverCircuit.coverCircuit 42 es (List.range 21)

set_option maxHeartbeats 0 in
theorem upper : Monotone2 witness ∧ witness.size = 124 ∧
    ∀ x : Fin 42 → Bool, witness.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 42, (u.val,v.val) ∈ es ∧ x u = true ∧ x v = true := by
  refine ⟨?_,by decide +kernel,?_⟩
  · intro g hg
    obtain ⟨op,len⟩ := CoverCircuit.gates_ops 42 es (List.range 21) g hg
    change (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2
    exact ⟨op.symm,len.le⟩
  · intro x
    have bounds : ∀ e ∈ es, e.1 < 42 ∧ e.2 < 42 := by decide +kernel
    have covered : ∀ e ∈ es, e.1 ∈ List.range 21 ∨ e.2 ∈ List.range 21 := by decide +kernel
    have evaluates := congrFun (CoverCircuit.circuitFun_eq 42 es (List.range 21) bounds covered) x
    change circuitFun 42 witness x = true ↔ _
    rw [show circuitFun 42 witness x = _ from evaluates,decide_eq_true_eq]
    constructor
    · rintro ⟨u,v,h,hu,hv⟩
      rcases h with h | h
      · exact ⟨u,v,h,hu,hv⟩
      · exact ⟨v,u,h,hv,hu⟩
    · rintro ⟨u,v,h,hu,hv⟩
      exact ⟨u,v,Or.inl h,hu,hv⟩

end PuncturedPlane
