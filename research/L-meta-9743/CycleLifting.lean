import PEqualNP.MetaComplexity.L106
import PEqualNP.MetaComplexity.Helpers.Elim
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace CycleLifting

open PEqualNP.MetaComplexity

abbrev Bits (n : ℕ) := Fin n → Bool
def row {n : ℕ} (s : Finset ℕ) : Bits n := fun i => decide (i.val ∈ s)
def pad {n N : ℕ} (x : Bits n) : Bits N := fun i => if h : i.val < n then x ⟨i.val,h⟩ else false

theorem padRow {n N : ℕ} (s : Finset ℕ) (bounded : ∀ a ∈ s, a < n) :
    (pad (row s : Bits n) : Bits N) = row s := by
  funext i
  by_cases h : i.val < n
  · simp [pad,row,h]
  · have miss : i.val ∉ s := fun hi => h (bounded _ hi)
    simp [pad,row,h,miss]

theorem padSnoc {n N : ℕ} (x : Bits n) : (pad (Fin.snoc x false) : Bits N) = pad x := by
  funext i
  by_cases h : i.val < n
  · have hs : i.val < n+1 := by omega
    simp only [pad,h,hs,dite_true]
    exact Fin.snoc_castSucc (α := fun _ => Bool) false x ⟨i.val,h⟩
  · by_cases hi : i.val = n
    · have hs : i.val < n+1 := by omega
      simp only [pad,h,hs,dite_true,dite_false]
      have hl : (⟨i.val,hs⟩ : Fin (n+1)) = Fin.last n := Fin.ext hi
      rw [hl,Fin.snoc_last]
    · have hs : ¬i.val < n+1 := by omega
      simp [pad,h,hs]

theorem shave {N k s : ℕ} (f : Bits N → Bool) (lo : 2 ≤ k)
    (j : ℕ) (hj : j < k) (one : f (row {j}) = false)
    (pair : f (row {k,j}) = true) (zero : f (row ∅) = false)
    (start : f (row {0,1}) = true)
    (h : HasCircuitSize (k+1) (fun x => f (pad x)) (s+1)) :
    HasCircuitSize k (fun x => f (pad x)) s := by
  have hd : ∃ x : Bits (k+1), f (pad (Function.update x (Fin.last k) (!x (Fin.last k)))) ≠
      f (pad x) := by
    refine ⟨row {j}, ?_⟩
    have he : Function.update (row {j}) (Fin.last k) (!(row {j} (Fin.last k))) =
        (row {k,j} : Bits (k+1)) := by
      funext i
      by_cases hp : i = Fin.last k
      · subst i
        simp [row, Fin.val_last, Nat.ne_of_gt hj]
      · have hv : i.val ≠ k := fun e => hp (Fin.ext e)
        simp [Function.update_of_ne hp,row,hv]
    rw [he,padRow,padRow,pair,one]
    · decide
    · simp
      omega
    · simp
      omega
  have hn : ∃ a b : Bits k, f (pad (Fin.snoc a false)) ≠ f (pad (Fin.snoc b false)) := by
    refine ⟨row ∅,row {0,1},?_⟩
    rw [padSnoc,padSnoc,padRow,padRow,zero,start]
    · decide
    · simp
      omega
    · simp
  simpa only [padSnoc] using Helpers.gate_elim k (fun x => f (pad x)) false s hd hn h

abbrev Cycle {b : ℕ} (x : Bits b) : Prop :=
  ∃ i j : Fin b, (i.val + 1) % b = j.val ∧ x i = true ∧ x j = true

theorem liftCycle {N b s : ℕ} (hb : 5 ≤ b) (hN : b ≤ N) (f : Bits N → Bool)
    (zero : f (row ∅) = false) (start : f (row {0,1}) = true)
    (one : ∀ j < N, f (row {j}) = false)
    (attach : ∀ k, b ≤ k → k < N → ∃ j < k, f (row {k,j}) = true)
    (base : ∀ x : Bits b, f (pad x) = decide (Cycle x)) (full : HasCircuitSize N f s) :
    N + (b+1)/2 ≤ s+1 := by
  let B := b + (b+1)/2 - 2
  have bad : ∀ t : ℕ, b+t ≤ N → ¬ HasCircuitSize (b+t) (fun x => f (pad x)) (B+t) := by
    intro t
    induction t with
    | zero =>
      intro _ h
      change HasCircuitSize b (fun x => f (pad x)) B at h
      simp only [base] at h
      have hbound := (L106 b B hb).1 h
      dsimp [B] at hbound
      omega
    | succ t ih =>
      intro hn h
      obtain ⟨j,hj,hp⟩ := attach (b+t) (by omega) (by omega)
      apply ih (by omega)
      exact shave f (by omega) j hj (one _ (by omega)) hp zero start h
  have eqN : b+(N-b) = N := by omega
  have hn := bad (N-b) (by omega)
  rw [eqN] at hn
  have idN (x : Bits N) : pad x = x := by funext i; simp [pad,i.isLt]
  simp only [idN] at hn
  by_contra! small
  obtain ⟨C,hC,hs,he⟩ := full
  apply hn
  refine ⟨C,hC,?_,he⟩
  dsimp [B]
  omega

def graphFun {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (x : Bits N) : Bool :=
  decide (∃ u v : Fin N, G.Adj u v ∧ x u = true ∧ x v = true)

theorem onGraph {N b s : ℕ} (hb : 5 ≤ b) (hN : b ≤ N) (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj]
    (core : ∀ i j : Fin b, G.Adj (Fin.castLE hN i) (Fin.castLE hN j) ↔
      (i.val+1)%b = j.val ∨ (j.val+1)%b = i.val)
    (attached : ∀ v : Fin N, b ≤ v.val → ∃ w : Fin N, w.val < v.val ∧ G.Adj v w)
    (circ : HasCircuitSize N (graphFun G) s) : N + (b+1)/2 ≤ s+1 := by
  apply liftCycle hb hN (graphFun G) _ _ _ _ _ circ
  · simp [graphFun,row]
  · let a : Fin b := ⟨0,by omega⟩
    let d : Fin b := ⟨1,by omega⟩
    have h := (core a d).2 (Or.inl (by simp [a,d,Nat.mod_eq_of_lt (by omega : 1 < b)]))
    apply decide_eq_true
    exact ⟨Fin.castLE hN a, Fin.castLE hN d, h, by simp [row,a], by simp [row,d]⟩
  · intro j _
    apply decide_eq_false
    rintro ⟨u,v,h,hu,hv⟩
    simp [row] at hu hv
    exact G.loopless.irrefl u ((Fin.ext (hu.trans hv.symm) : u = v) ▸ h)
  · intro k lo hi
    obtain ⟨w,hw,edge⟩ := attached ⟨k,hi⟩ lo
    refine ⟨w.val,hw,decide_eq_true ?_⟩
    exact ⟨⟨k,hi⟩,w,edge,by simp [row],by simp [row]⟩
  · intro x
    apply decide_eq_decide.mpr
    constructor
    · rintro ⟨u,v,edge,hu,hv⟩
      have small (z : Fin N) (hz : pad x z = true) : z.val < b := by
        by_contra hn
        simp [pad,hn] at hz
      let i : Fin b := ⟨u.val,small u hu⟩
      let j : Fin b := ⟨v.val,small v hv⟩
      have xi : x i = true := by simpa only [pad,dite_eq_left (small u hu)] using hu
      have xj : x j = true := by simpa only [pad,dite_eq_left (small v hv)] using hv
      rcases (core i j).1 edge with eq | eq
      · exact ⟨i,j,eq,xi,xj⟩
      · exact ⟨j,i,eq,xj,xi⟩
    · rintro ⟨i,j,eq,hi,hj⟩
      refine ⟨Fin.castLE hN i,Fin.castLE hN j,(core i j).2 (Or.inl eq),?_,?_⟩
      · simpa [pad,i.isLt] using hi
      · simpa [pad,j.isLt] using hj

end CycleLifting
