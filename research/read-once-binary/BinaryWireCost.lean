import BinarySubstitution
import PairedExact

namespace Paired.Split
open PEqualNP.MetaComplexity

def listed (keys : List Coord) (f : Wire) (k : ℕ) : Prop :=
  ∃ C : BinaryCircuit, C.size ≤ k ∧ ∀ x : Row, C.eval (keys.map x) = f x

theorem read_available (gs : List BinaryGate) (v : List Bool) (i : ℕ) (hi : i < v.length) :
    (run gs v).getD i false = v.getD i false := by
  induction gs generalizing v with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (bitStep v g)).getD i false = _
    rw [ih (bitStep v g) (by simp [bitStep]; omega)]
    exact List.getD_append _ _ _ _ hi

def invertedPrefix : List BinaryGate → ℕ → List BinaryGate
  | [],_ => []
  | g::_,0 => [⟨fun a b => !(g.op a b),g.left,g.right⟩]
  | g::gs,j+1 => g::invertedPrefix gs j

theorem inverted_length (gs : List BinaryGate) (j : ℕ) : (invertedPrefix gs j).length ≤ gs.length := by
  induction gs generalizing j with
  | nil => simp [invertedPrefix]
  | cons g gs ih => cases j <;> simp [invertedPrefix,ih]

theorem inverted_value (gs : List BinaryGate) {j : ℕ} (hj : j < gs.length) (v : List Bool) :
    (run (invertedPrefix gs j) v).getD (v.length+j) false = !(run gs v).getD (v.length+j) false := by
  induction gs generalizing j v with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero]
      change (bitStep v ⟨_,g.left,g.right⟩).getD v.length false = !(run gs (bitStep v g)).getD v.length false
      rw [read_available gs _ _ (by simp [bitStep])]
      simp [bitStep]
    | succ j =>
      have small : j < gs.length := by simpa using hj
      have next := ih small (bitStep v g)
      simpa [invertedPrefix,run,bitStep,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using next

theorem no_primary {f : Wire} {p q : Coord} (pq : p ≠ q) (ep : essential f p) (eq : essential f q)
    (v : Coord) : normalize f ≠ input v := by
  intro same
  have force {i : Coord} (ei : essential f i) : v = i := by
    obtain ⟨x,y,d,others⟩ := ei
    have diff := normalize_diff d
    rw [same] at diff
    by_contra ne
    exact diff (others v ne)
  exact pq ((force ep).symm.trans (force eq))

theorem listed_iff_native (keys : List Coord) {f : Wire} {p q : Coord} (pq : p ≠ q)
    (ep : essential f p) (eq : essential f q) (k : ℕ) : listed keys f k ↔ native keys f k := by
  constructor
  · rintro ⟨C,bd,ev⟩
    exact ⟨C,(cost_le C).trans bd,ev⟩
  · intro h
    have feasible := (native_iff keys f k (nonzero_of_essential ep)).mp h
    obtain ⟨gs,bd,i,hi,ev⟩ := realize_build feasible keys [] (initial_realized keys)
    simp only [List.nil_append] at hi ev
    cases base : f baseline
    · refine ⟨⟨gs,i⟩,bd,?_⟩
      intro x
      change (run gs (keys.map x)).getD i false = f x
      simpa [normalize,base] using ev x
    · have internal : keys.length ≤ i := by
        by_contra! small
        apply no_primary pq ep eq keys[i]
        funext x
        have original := ev x
        rw [read_available gs _ _ (by simpa using small),List.getD_eq_getElem _ _ (by simpa using small),
          List.getElem_map] at original
        exact original.symm
      let j := i-keys.length
      have ji : keys.length+j=i := by dsimp [j]; omega
      have valid : j < gs.length := by omega
      refine ⟨⟨invertedPrefix gs j,i⟩,(inverted_length gs j).trans bd,?_⟩
      intro x
      have invert := inverted_value gs valid (keys.map x)
      rw [List.length_map,ji,ev x] at invert
      change (run (invertedPrefix gs j) (keys.map x)).getD i false = f x
      simpa [normalize,base] using invert

end Paired.Split
