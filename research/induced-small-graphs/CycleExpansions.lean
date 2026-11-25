import InducedCycle

namespace CycleCircuit
open Paired Paired.Split

def neighborOnly (i : Fin 5) (p : Coord) : Bool := decide (p = coord (i+1))
def bothOn (i : Fin 5) (p : Coord) : Bool := decide (p = coord i ∨ p = coord (i+1))

theorem core_essential (p : Coord) (hp : p ∈ keys) : essential fn p := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
  have diff : ∀ j : Fin 5, fn (neighborOnly j) ≠ fn (bothOn j) := by decide +kernel
  refine ⟨neighborOnly i,bothOn i,diff i,?_⟩
  intro q qp
  simp [neighborOnly,bothOn,qp]

theorem core_supported : supported keys.toFinset fn := by
  intro x y eq
  apply congrArg spec
  funext i
  exact eq _ (List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨i,rfl⟩))

-- Restricting the gate choice to OR at every step gives exactly the independent vertex blow-ups.
inductive Expanded : List Coord → Wire → ℕ → Prop where
  | core : Expanded keys fn 0
  | splitInput {list f d p q} (previous : Expanded list f d) (hp : p ∈ list) (hq : q ∉ list) (t : Bool) :
      Expanded (q::list) (split f t p q) (d+1)

theorem expansion_inputs {list f d} (h : Expanded list f d) :
    list.Nodup ∧ supported list.toFinset f ∧ ∀ p ∈ list, essential f p := by
  induction h with
  | core => exact ⟨by decide,core_supported,core_essential⟩
  | @splitInput list f d p q _ hp hq t ih =>
    obtain ⟨nd,sup,ess⟩ := ih
    have fresh : q ∉ list.toFinset := by simpa using hq
    have present := List.mem_toFinset.mpr hp
    refine ⟨List.nodup_cons.mpr ⟨hq,nd⟩,?_,?_⟩
    · simpa only [List.toFinset_cons] using support_split sup present (q := q) t
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | old
      · exact fresh_essential sup present fresh t (ess _ hp)
      · exact preserve_essential sup fresh t (ess _ old)

theorem expansion_native {list f d} (h : Expanded list f d) (k : ℕ) :
    native list f k ↔ 7+d ≤ k := by
  induction h generalizing k with
  | core => exact exact_size k
  | @splitInput list f d p q prev hp hq t ih =>
    obtain ⟨_,sup,ess⟩ := expansion_inputs prev
    cases k with
    | succ k =>
      rw [native_split_iff list sup hp hq t (ess p hp) k,ih]
      omega
    | zero =>
      constructor
      · intro run
        have nz := nonzero_of_essential (fresh_essential sup (List.mem_toFinset.mpr hp)
          (show q ∉ list.toFinset by simpa using hq) t (ess p hp))
        have build := (native_iff _ _ _ nz).mp run
        rw [List.toFinset_cons] at build
        have hq' : q ∉ list.toFinset := by simpa using hq
        obtain ⟨l,bd,_⟩ := split_lower sup (List.mem_toFinset.mpr hp) hq' t (ess p hp) build
        omega
      · omega

theorem expansion_mono {list f d} (h : Expanded list f d) : mono list f (7+d) := by
  induction h with
  | core => exact upper
  | @splitInput list f d p q prev hp _ t ih =>
    exact mono_split (expansion_inputs prev).1 hp q t ih

theorem expansion_length {list f d} (h : Expanded list f d) : list.length = 5+d := by
  induction h with
  | core => rfl
  | splitInput _ _ _ _ ih => simp [ih,Nat.add_assoc]

end CycleCircuit
