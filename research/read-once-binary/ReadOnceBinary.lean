import BinaryWireCost
import PairedExpansion
import CycleExpansions

namespace Paired.Split
open PEqualNP.MetaComplexity

inductive Refined (initial : List Coord) (base : Wire) : List Coord → Wire → ℕ → Prop where
  | start : Refined initial base initial base 0
  | extend {keys f d p q} (before : Refined initial base keys f d) (hp : p ∈ keys) (hq : q ∉ keys)
      (o : Op) (binary : both o = true) : Refined initial base (q::keys) (composeInput f o p q) (d+1)

theorem refined_inputs {start base keys f d} (h : Refined start base keys f d)
    (sup : supported start.toFinset base) (ess : ∀ p ∈ start, essential base p) :
    supported keys.toFinset f ∧ ∀ p ∈ keys, essential f p := by
  induction h with
  | start => exact ⟨sup,ess⟩
  | @extend before g _ p q _ hp hq o binary ih =>
    obtain ⟨old,used⟩ := ih
    have hp' := List.mem_toFinset.mpr hp
    have hq' : q ∉ before.toFinset := by simpa using hq
    refine ⟨by simpa using compose_supported (q := q) old hp' o,?_⟩
    intro i hi
    rcases List.mem_cons.mp hi with rfl | mem
    · exact new_input_essential old hp' hq' binary (used _ hp)
    · exact old_input_essential old hp' hq' binary (used _ mem)

theorem refined_contains {start base keys f d} (h : Refined start base keys f d) : start ⊆ keys := by
  induction h with
  | start => exact fun _ a => a
  | extend _ _ _ _ _ ih => exact fun _ a => List.mem_cons_of_mem _ (ih a)

theorem refined_length {start base keys f d} (h : Refined start base keys f d) :
    keys.length = start.length+d := by
  induction h with
  | start => rfl
  | extend _ _ _ _ _ ih => simp [ih,Nat.add_assoc]

theorem refined_native {start base keys f d} (h : Refined start base keys f d)
    (sup : supported start.toFinset base) (ess : ∀ p ∈ start, essential base p)
    {c : ℕ} (opt : ∀ k, native start base k ↔ c ≤ k) (k : ℕ) :
    native keys f k ↔ c+d ≤ k := by
  induction h generalizing k with
  | start => exact opt k
  | @extend before g _ p q prev hp hq o binary ih =>
    obtain ⟨old,used⟩ := refined_inputs prev sup ess
    cases k with
    | succ k =>
      rw [compose_iff before old hp hq binary (used _ hp) k,ih]
      omega
    | zero =>
      constructor
      · intro h
        obtain ⟨l,bd,_⟩ := compose_lower before old hp hq binary (used _ hp) h
        omega
      · omega

theorem refined_listed {start base keys f d} (h : Refined start base keys f d)
    (sup : supported start.toFinset base) (ess : ∀ p ∈ start, essential base p)
    {p q : Coord} (hp : p ∈ start) (hq : q ∈ start) (pq : p ≠ q)
    {c : ℕ} (opt : ∀ k, native start base k ↔ c ≤ k) (k : ℕ) :
    listed keys f k ↔ c+d ≤ k := by
  have all := (refined_inputs h sup ess).2
  rw [listed_iff_native keys pq (all p (refined_contains h hp)) (all q (refined_contains h hq))]
  exact refined_native h sup ess opt k

theorem one_supported (p : Coord) : supported [p].toFinset (input p) := by
  intro x y eq
  exact eq p (by simp)

theorem one_essential (p : Coord) : ∀ i ∈ [p], essential (input p) i := by
  intro i hi
  have hit : i = p := List.mem_singleton.mp hi
  subst i
  refine ⟨(fun _ => false),(fun v => decide (v = p)),by simp [input],?_⟩
  intro v vp
  simp [vp]

theorem one_upper (p : Coord) (k : ℕ) : listed [p] (input p) k :=
  ⟨⟨[],0⟩,Nat.zero_le _,fun _ => rfl⟩

theorem one_native (p : Coord) (k : ℕ) : native [p] (input p) k ↔ 0 ≤ k :=
  ⟨fun _ => Nat.zero_le _,fun _ => ⟨⟨[],0⟩,Nat.zero_le _,fun _ => rfl⟩⟩

theorem read_once_size (p : Coord) {keys f d} (h : Refined [p] (input p) keys f d) (k : ℕ) :
    listed keys f k ↔ d ≤ k := by
  cases h with
  | start => exact ⟨fun _ => Nat.zero_le _,fun _ => one_upper p k⟩
  | @extend before g steps old fresh prev hp hq o binary =>
    have next := Refined.extend prev hp hq o binary
    have two := (refined_inputs next (one_supported p) (one_essential p)).2
    have ne : old ≠ fresh := fun e => hq (e ▸ hp)
    rw [listed_iff_native _ ne (two old (List.mem_cons_of_mem _ hp)) (two fresh (by simp))]
    simpa using refined_native next (one_supported p) (one_essential p) (one_native p) k

theorem paired_mixed {n : ℕ} (hn : 2 ≤ n) {keys f d}
    (h : Refined (labels n) (value (Finset.range n)) keys f d) (k : ℕ) :
    listed keys f k ↔ 3*n+d ≤ k+2 := by
  have opt (j : ℕ) : native (labels n) (value (Finset.range n)) j ↔ 3*n-2 ≤ j := by
    rw [central_native hn]; omega
  have present (b : Bool) : (0,b) ∈ labels n := (label_mem n (0,b)).mpr (by dsimp; omega)
  rw [refined_listed h (base_supported n) (fun _ hp => base_essential hn hp)
    (present false) (present true) (by decide) opt]
  omega

theorem cycle_mixed {keys f d} (h : Refined CycleCircuit.keys CycleCircuit.fn keys f d) (k : ℕ) :
    listed keys f k ↔ 7+d ≤ k :=
  refined_listed h CycleCircuit.core_supported CycleCircuit.core_essential
    (p := (0,false)) (q := (1,false)) (by decide) (by decide) (by decide) CycleCircuit.exact_size k

end Paired.Split
