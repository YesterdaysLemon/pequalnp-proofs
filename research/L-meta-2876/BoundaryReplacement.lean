import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.LowMergeWires
import Mathlib.Order.Preorder.Finite

namespace HeawoodBoundaryReplacement

variable {X W : Type*} [Preorder X] [Preorder W]

-- The external inputs and the wires in the replaced bank may both feed K.
-- The replacement may improve either sign on the corresponding boundary.
theorem replaceBank [Finite X] (target : X → Prop) (K : X → W → Prop)
    (old new : X → W) (external : ∀ w, Monotone (fun x => K x w))
    (internal : ∀ x, Monotone (K x)) (newMono : Monotone new)
    (correct : ∀ x, K x (old x) ↔ target x)
    (lower : ∀ x, Minimal target x → old x ≤ new x)
    (upper : ∀ x, Maximal (fun x => ¬target x) x → new x ≤ old x) :
    ∀ x, K x (new x) ↔ target x := by
  have composed : Monotone (fun x => K x (new x)) := by
    intro x y hxy
    exact (external (new x) hxy).trans (internal y (newMono hxy))
  intro x
  constructor
  · intro h
    by_contra hn
    obtain ⟨y, hxy, hy⟩ := Finite.exists_le_maximal (p := fun z => ¬target z) hn
    exact hy.1 ((correct y).1 ((internal y (upper y hy)) (composed hxy h)))
  · intro h
    obtain ⟨y, hyx, hy⟩ := Finite.exists_le_maximal (α := OrderDual X) (p := target) h
    exact composed hyx ((internal y (lower y hy)) ((correct y).2 hy.1))

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem replaceCircuitBank [Finite X] {n : ℕ} (target : X → Prop) (C : Circuit)
    (hm : Monotone2 C) (old new : X → Fin n → Bool) (newMono : Monotone new)
    (correct : ∀ x, C.eval (List.ofFn (old x)) = true ↔ target x)
    (lower : ∀ x, Minimal target x → old x ≤ new x)
    (upper : ∀ x, Maximal (fun x => ¬target x) x → new x ≤ old x) :
    ∀ x, C.eval (List.ofFn (new x)) = true ↔ target x := by
  apply replaceBank target (fun _ z => C.eval (List.ofFn z) = true)
    old new (fun _ _ _ _ h => h) _ newMono correct lower upper
  intro _ a b hab
  have hc : IsMonotoneCircuit C := fun g hg => (hm g hg).1
  apply LowMergeProof.wires_mono C hc _ _ (by simp) _ C.output
  intro i hi
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h] at hi ⊢
    exact Bool.le_iff_imp.mp (hab ⟨i, h⟩) hi
  · simp [List.getD_eq_getElem?_getD, h] at hi

variable {V : Type*} [DecidableEq V]

def hits (E : V → V → Prop) (s : Finset V) : Prop :=
  ∃ a ∈ s, ∃ b ∈ s, E a b

-- The graph may be infinite. The proof only uses a two-vertex witness.
theorem eraseOnEdges (E : V → V → Prop) (u : Finset V → Prop)
    (K : Finset V → Prop → Prop) (external : ∀ w, Monotone (fun s => K s w))
    (internal : ∀ s, Monotone (K s)) (correct : ∀ s, K s (u s) ↔ hits E s)
    (dead : ∀ a b, E a b → ¬ u {a, b}) : ∀ s, K s False ↔ hits E s := by
  intro s
  constructor
  · intro h
    exact (correct s).1 ((internal s (show False ≤ u s from False.elim)) h)
  · rintro ⟨a, ha, b, hb, edge⟩
    have hsub : ({a, b} : Finset V) ⊆ s := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact ha
      · exact Finset.mem_singleton.mp hz ▸ hb
    have hsmall : hits E {a, b} := ⟨a, by simp, b, by simp, edge⟩
    have h := (correct {a, b}).2 hsmall
    rw [propext (iff_false_intro (dead a b edge))] at h
    exact external False hsub h

theorem eraseNonedgeAnd (E : V → V → Prop) (i j : V) (ne : i ≠ j)
    (forward : ¬E i j) (backward : ¬E j i) (K : Finset V → Prop → Prop)
    (external : ∀ w, Monotone (fun s => K s w)) (internal : ∀ s, Monotone (K s))
    (correct : ∀ s, K s (i ∈ s ∧ j ∈ s) ↔ hits E s) :
    ∀ s, K s False ↔ hits E s := by
  apply eraseOnEdges E (fun s => i ∈ s ∧ j ∈ s) K external internal correct
  intro a b edge both
  simp only [Finset.mem_insert, Finset.mem_singleton] at both
  rcases both with ⟨(rfl | rfl), (rfl | rfl)⟩ <;> tauto

-- A complete-star wire is false off the graph function. A larger union of
-- complete stars can replace it simultaneously wherever it occurs.
omit [Preorder X] in
theorem enlargeSafeWire (target : X → Prop) (K : X → Prop → Prop)
    (old new : X → Prop) (internal : ∀ x, Monotone (K x))
    (correct : ∀ x, K x (old x) ↔ target x)
    (includes : ∀ x, old x → new x) (safe : ∀ x, new x → target x) :
    ∀ x, K x (new x) ↔ target x := by
  intro x
  constructor
  · intro h
    by_cases v : new x
    · exact safe x v
    · exact (correct x).1 ((internal x (show new x ≤ old x from fun hn => (v hn).elim)) h)
  · exact fun h => internal x (includes x) ((correct x).2 h)

end HeawoodBoundaryReplacement
