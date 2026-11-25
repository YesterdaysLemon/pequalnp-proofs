import PEqualNP.MetaComplexity.Helpers.Parity

namespace PendantPath

open PEqualNP.MetaComplexity
abbrev Bits (n : ℕ) := Fin n → Bool

def extend {n : ℕ} (f : Bits n → Bool) (w : Fin n) (z : Bits (n+2)) : Bool :=
  let x := fun i : Fin n => z i.castSucc.castSucc
  f x || (z (Fin.last n).castSucc && (z (Fin.last (n+1)) || x w))

theorem eval {n : ℕ} (f : Bits n → Bool) (w : Fin n) (x : Bits n) (v u : Bool) :
    extend f w (Fin.snoc (Fin.snoc x v) u) = (f x || (v && (u || x w))) := by
  simp [extend]

theorem weaken {n s t : ℕ} {f : Bits n → Bool} (h : HasCircuitSize n f s) (le : s ≤ t) :
    HasCircuitSize n f t := by
  obtain ⟨C,hm,hs,hf⟩ := h
  exact ⟨C,hm,hs.trans le,hf⟩

theorem lastDepends {n : ℕ} {g : Bits (n+1) → Bool} (y : Bits n)
    (different : g (Fin.snoc y true) ≠ g (Fin.snoc y false)) :
    ∃ x, g (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ g x := by
  refine ⟨Fin.snoc y false,?_⟩
  have e : Function.update (Fin.snoc (α := fun _ => Bool) y false) (Fin.last n)
      (!(Fin.snoc (α := fun _ => Bool) y false (Fin.last n))) =
      Fin.snoc (α := fun _ => Bool) y true := by
    funext i
    induction i using Fin.lastCases with
    | last => simp
    | cast j => simp
  rw [e]
  exact different

-- In the extension v is the neighbor of the new leaf u and the old vertex w.
-- Each fixed value of u leaves a function that still depends on v.
theorem saveThree {n s : ℕ} (f : Bits n → Bool) (w : Fin n)
    (off on positive : Bits n) (hoff : f off = false) (hw0 : off w = false)
    (hon : f on = false) (hw1 : on w = true) (yes : f positive = true)
    (h : HasCircuitSize (n+2) (extend f w) (s+3)) : HasCircuitSize n f s := by
  have dep := lastDepends (g := extend f w) (Fin.snoc off true)
    (by simp [eval,hoff,hw0])
  have nc (u : Bool) : ∃ a b : Bits (n+1),
      extend f w (Fin.snoc a u) ≠ extend f w (Fin.snoc b u) := by
    refine ⟨Fin.snoc off false,Fin.snoc positive false,?_⟩
    simp [eval,hoff,yes]
  obtain ⟨u,t,ht,small⟩ := Helpers.gate_elim_two (n+1) (extend f w) (s+3) dep nc h
  let g : Bits (n+1) → Bool := fun z => extend f w (Fin.snoc z u)
  have small' : HasCircuitSize (n+1) g (s+1) := weaken small (by omega)
  have dv := lastDepends (g := g) on (by simp [g,eval,hon,hw1])
  have ncv : ∃ a b : Bits n, g (Fin.snoc a false) ≠ g (Fin.snoc b false) := by
    exact ⟨off,positive,by simp [g,eval,hoff,yes]⟩
  have reduced := Helpers.gate_elim n g false s dv ncv small'
  simpa [g,eval] using reduced

theorem transfer {n k s : ℕ} (f : Bits n → Bool) (w : Fin n)
    (off on positive : Bits n) (hoff : f off = false) (hw0 : off w = false)
    (hon : f on = false) (hw1 : on w = true) (yes : f positive = true)
    (hk : 0 < k) (lower : ∀ t, HasCircuitSize n f t → k ≤ t)
    (h : HasCircuitSize (n+2) (extend f w) s) : k+3 ≤ s := by
  by_contra! small
  have r := saveThree (s := k-1) f w off on positive hoff hw0 hon hw1 yes (weaken h (by omega))
  have impossible := lower (k-1) r
  omega

end PendantPath
