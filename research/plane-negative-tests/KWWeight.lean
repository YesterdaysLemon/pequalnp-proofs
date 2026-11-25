import KWPartition
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace KWWeight
open KWPartition
variable {R C V : Type} [DecidableEq R] [DecidableEq C]

def mass (w : R → C → Int) (A : Finset R) (B : Finset C) : Int := ∑ i ∈ A, ∑ j ∈ B, w i j

theorem split_rows (w : R → C → Int) (A : Finset R) (B : Finset C) (p : R → Bool) :
    mass w (A.filter (fun r => p r=true)) B + mass w (A.filter (fun r => p r=false)) B = mass w A B := by
  simpa [mass] using Finset.sum_filter_add_sum_filter_not A (fun r => p r = true) (fun i => ∑ j ∈ B, w i j)

theorem split_cols (w : R → C → Int) (A : Finset R) (B : Finset C) (p : C → Bool) :
    mass w A (B.filter (fun c => p c=false)) + mass w A (B.filter (fun c => p c=true)) = mass w A B := by
  simp only [mass,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simpa using Finset.sum_filter_add_sum_filter_not B (fun c => p c = false) (w i)

theorem lower (yes : R → V → Bool) (no : C → V → Bool) (w : R → C → Int) (D : Int)
    (bound : ∀ v A B, (∀ i ∈ A, yes i v = true) → (∀ j ∈ B, no j v = false) → mass w A B ≤ D)
    (f : Formula V) (A : Finset R) (B : Finset C)
    (pos : ∀ i ∈ A, f.eval (yes i) = true) (neg : ∀ j ∈ B, f.eval (no j) = false) :
    mass w A B ≤ D * (f.leaves : Int) := by
  induction f generalizing A B with
  | var v => simpa [Formula.leaves] using bound v A B pos neg
  | join l r hl hr =>
    have left := hl (A.filter (fun i => l.eval (yes i) = true)) B
      (fun _ h => (Finset.mem_filter.mp h).2) (fun j hj => (Bool.or_eq_false_iff.mp (neg j hj)).1)
    have right := hr (A.filter (fun i => l.eval (yes i) = false)) B
      (fun i h => by obtain ⟨hi,z⟩ := Finset.mem_filter.mp h; simpa [Formula.eval,z] using pos i hi)
      (fun j hj => (Bool.or_eq_false_iff.mp (neg j hj)).2)
    have add := add_le_add left right
    simpa only [split_rows,Formula.leaves,Int.natCast_add,Int.mul_add] using add
  | meet l r hl hr =>
    have left := hl A (B.filter (fun j => l.eval (no j) = false))
      (fun i hi => (Bool.and_eq_true_iff.mp (pos i hi)).1) (fun _ h => (Finset.mem_filter.mp h).2)
    have right := hr A (B.filter (fun j => l.eval (no j) = true))
      (fun i hi => (Bool.and_eq_true_iff.mp (pos i hi)).2)
      (fun j h => by obtain ⟨hj,z⟩ := Finset.mem_filter.mp h; simpa [Formula.eval,z] using neg j hj)
    have add := add_le_add left right
    simpa only [split_cols,Formula.leaves,Int.natCast_add,Int.mul_add] using add

theorem cap (w : R → C → Int) (A : Finset R) (B J : Finset C) (sub : B ⊆ J) :
    mass w A B ≤ ∑ c ∈ J, max 0 (∑ r ∈ A, w r c) := by
  rw [mass, Finset.sum_comm]
  exact (Finset.sum_le_sum (fun c _ => le_max_right 0 _)).trans
    (Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => le_max_left 0 _))

end KWWeight
