import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace TestCounts
/-- A cover of exactly the fractional lower bound must use only saturated pieces.
    If every saturated piece contributes a multiple of d to one component, this
    forces the total required value of that component to be a multiple of d. -/
theorem strict_count {ι : Type} (s : Finset ι) (u v : ι → Nat) (w U V D K d : Nat)
    (hw : 0<w) (mass : w*U+V=K*D)
    (hu : U ≤ ∑ i ∈ s, u i) (hv : V ≤ ∑ i ∈ s, v i)
    (cap : ∀ i ∈ s, w*u i + v i ≤ D)
    (sat : ∀ i ∈ s, w*u i + v i = D → d ∣ u i) (nd : ¬d ∣ U) : K<s.card := by
  classical
  by_contra no
  have small : s.card ≤ K := by omega
  have wm := Nat.mul_le_mul_left w hu
  have room := Nat.mul_le_mul_right D small
  have bound := Finset.sum_le_sum cap
  have full : ∑ i ∈ s, (w*u i + v i) = K*D := by
    simp only [Finset.sum_add_distrib,← Finset.mul_sum] at bound ⊢
    simp only [Finset.sum_const,Nat.nsmul_eq_mul] at bound
    omega
  have all : ∀ i ∈ s, w*u i+v i=D := by
    intro i hi
    by_contra bad
    have strict := Finset.sum_lt_sum cap ⟨i,hi,lt_of_le_of_ne (cap i hi) bad⟩
    rw [full] at strict
    simp only [Finset.sum_const,Nat.nsmul_eq_mul] at strict
    omega
  have eqs : (∑ i ∈ s, u i) = U := by
    by_contra bad
    have diff : U < ∑ i ∈ s, u i := by omega
    have change := Nat.mul_lt_mul_of_pos_left diff hw
    simp only [Finset.sum_add_distrib,← Finset.mul_sum] at full
    omega
  apply nd
  rw [← eqs]
  exact Finset.dvd_sum fun i hi => sat i hi (all i hi)

def pairs (p : Nat) := p*(p-1)/2

theorem fano_capacity : ∀ a b : Fin 8, (a.val+2)*(b.val+2) ≤ 18 →
    pairs a + pairs b + 4*a.val*b.val ≤ 22 ∧
    (pairs a + pairs b + 4*a.val*b.val = 22 → 6 ∣ pairs a) := by decide +kernel

theorem plane_capacity : ∀ a b : Fin 22, (a.val+4)*(b.val+4) ≤ 100 →
    pairs a + pairs b + 5*a.val*b.val ≤ 210 ∧
    (pairs a + pairs b + 5*a.val*b.val = 210 → 36 ∣ a.val*b.val) := by decide +kernel

theorem fano_lower {ι : Type} (s : Finset ι) (p l : ι → Fin 8)
    (geom : ∀ i ∈ s, ((p i).val+2)*((l i).val+2) ≤ 18)
    (pp : 21 ≤ ∑ i ∈ s, pairs (p i)) (ll : 21 ≤ ∑ i ∈ s, pairs (l i))
    (pl : 28 ≤ ∑ i ∈ s, (p i).val*(l i).val) : 7<s.card := by
  apply strict_count s (fun i => pairs (p i)) (fun i => pairs (l i)+4*((p i).val*(l i).val))
    1 21 133 22 7 6 (by decide) (by decide) pp
  · simp only [Finset.sum_add_distrib,← Finset.mul_sum]
    omega
  · intro i hi
    simpa [Nat.mul_assoc,Nat.add_assoc] using (fano_capacity _ _ (geom i hi)).1
  · intro i hi h
    apply (fano_capacity _ _ (geom i hi)).2
    simpa [Nat.mul_assoc,Nat.add_assoc] using h
  · decide

theorem plane_lower {ι : Type} (s : Finset ι) (p l : ι → Fin 22)
    (geom : ∀ i ∈ s, ((p i).val+4)*((l i).val+4) ≤ 100)
    (pp : 210 ≤ ∑ i ∈ s, pairs (p i)) (ll : 210 ≤ ∑ i ∈ s, pairs (l i))
    (pl : 336 ≤ ∑ i ∈ s, (p i).val*(l i).val) : 10<s.card := by
  apply strict_count s (fun i => (p i).val*(l i).val) (fun i => pairs (p i)+pairs (l i))
    5 336 420 210 10 36 (by decide) (by decide) pl
  · simp only [Finset.sum_add_distrib]
    omega
  · intro i hi
    simpa [Nat.mul_assoc,add_comm,add_left_comm,add_assoc] using (plane_capacity _ _ (geom i hi)).1
  · intro i hi h
    apply (plane_capacity _ _ (geom i hi)).2
    simpa [Nat.mul_assoc,add_comm,add_left_comm,add_assoc] using h
  · decide
end TestCounts
