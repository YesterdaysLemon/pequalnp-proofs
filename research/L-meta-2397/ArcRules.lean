import PEqualNP.MetaComplexity.L107
import PEqualNP.MetaComplexity.Helpers.ForestElim
import PEqualNP.MetaComplexity.Helpers.PermInputs
import PEqualNP.MetaComplexity.Helpers.Support

namespace PlaneArcRules

open PEqualNP.MetaComplexity

abbrev Bits (n : ℕ) := Fin n → Bool
def restrict {n : ℕ} (f : Bits n → Bool) (p : Fin n) (b : Bool) : Bits n → Bool :=
  fun x => f (Function.update x p b)
def essential {n : ℕ} (f : Bits n → Bool) (p : Fin n) : Prop :=
  ∃ x, f (Function.update x p (!x p)) ≠ f x
def varies {n : ℕ} (f : Bits n → Bool) : Prop := ∃ x y, f x ≠ f y
def lower {n : ℕ} (f : Bits n → Bool) (k : ℕ) : Prop :=
  ∀ s, HasCircuitSize n f s → k ≤ s

theorem supportBound {n} {f : Bits n → Bool} (T : Finset (Fin n))
    (dep : ∀ i ∈ T, essential f i) : lower f (T.card-1) := by
  intro s h
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  let S := (Helpers.suppsFrom C.gates (Helpers.inputSupps n)).getD C.output ∅
  have sub : T ⊆ S := by
    intro i hi
    by_contra absent
    obtain ⟨x, hx⟩ := dep i hi
    apply hx
    have agree := (Helpers.agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (Helpers.agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have hki : k ≠ i := fun e => absent (e ▸ hk)
        simp [Function.update_of_ne hki])
    rw [← hev, ← hev]
    exact agree
  have hT := Finset.card_le_card sub
  have hc := Helpers.cnt_suppsFrom C.gates 0 (Helpers.inputSupps n) ok Helpers.cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  change S.card ≤ _ at hc
  omega

theorem fixedExcluded {n k} {f : Bits (n+1) → Bool} {p : Fin (n+1)} {b : Bool}
    (dep : essential f p) (nc : varies (restrict f p b))
    (child : ¬HasCircuitSize (n+1) (restrict f p b) k) :
    ¬HasCircuitSize (n+1) f (k+1) := fun h =>
  child (Helpers.Forest.one_gate_at n f p b k dep nc h)

theorem twoBranches {n k} {f : Bits (n+1) → Bool} {p : Fin (n+1)}
    (dep : essential f p) (nc : ∀ b, varies (restrict f p b))
    (children : ∀ b, lower (restrict f p b) k) : lower f (k+2) := by
  intro s h
  obtain ⟨b,t,small,ckt⟩ := Helpers.PermInputs.gate_elim_at n f p s dep nc h
  have bound := children b t ckt
  omega

def triple {n : ℕ} (f : Bits n → Bool) (p q : Fin n) : Prop :=
  ∃ a b : Bool, ∀ x : Bits n,
    f (Function.update (Function.update x p (!a)) q b) =
      f (Function.update (Function.update x p a) q (!b)) ∧
    f (Function.update (Function.update x p a) q (!b)) =
      f (Function.update (Function.update x p (!a)) q (!b))

theorem irrelevant {n} {f : Bits n → Bool} {p : Fin n} (h : ¬essential f p)
    (b : Bool) : restrict f p b = f := by
  funext x
  change f (Function.update x p b) = f x
  by_cases hb : b = x p
  · rw [hb, Function.update_eq_self]
  · have hflip : b = !x p := by cases b <;> cases hv : x p <;> simp_all
    rw [hflip]
    exact Classical.byContradiction (fun hne => h ⟨x,hne⟩)

theorem fanBranches {n k} {f : Bits (n+1) → Bool}
    (someDep : ∃ p, essential f p)
    (nc : ∀ p, essential f p → ∀ b, varies (restrict f p b))
    (unlinked : ∀ p q, p ≠ q → essential f p → essential f q → ¬triple f p q)
    (lo : ∀ p, essential f p → lower (restrict f p false) (k-3))
    (hi : ∀ p, essential f p → lower (restrict f p true) (k-4)) : lower f k := by
  classical
  intro s hs
  let existsCircuit : ∃ t, HasCircuitSize (n+1) f t := ⟨s, hs⟩
  let best := Nat.find existsCircuit
  have hbest : HasCircuitSize (n+1) f best := Nat.find_spec existsCircuit
  have least : ∀ t, HasCircuitSize (n+1) f t → best ≤ t := fun _ h => Nat.find_min' existsCircuit h
  have bs := least s hs
  have depOfSaving (p : Fin (n+1)) (b : Bool) (t : ℕ)
      (saved : t < best) (small : HasCircuitSize (n+1) (restrict f p b) t) : essential f p := by
    by_contra h
    rw [irrelevant h b] at small
    exact (Nat.not_le_of_lt saved) (least t small)
  rcases L107 n f best someDep nc unlinked hbest with ⟨p,t,h,c⟩ | ⟨p,t,h,c⟩
  · have hp := depOfSaving p false t (by omega) c
    have bound := lo p hp t c
    omega
  · have hp := depOfSaving p true t (by omega) c
    have bound := hi p hp t c
    omega

end PlaneArcRules
