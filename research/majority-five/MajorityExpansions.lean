import MajoritySizes
import FirstGateRestriction

namespace FiveMajority
open Paired Paired.Split PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def twoVotes (i : Fin 5) (p : Coord) : Bool := decide (p = coord (i+1) ∨ p = coord (i+2))
def threeVotes (i : Fin 5) (p : Coord) : Bool := twoVotes i p || decide (p = coord i)

theorem essential_input (p : Coord) (hp : p ∈ keys) : essential fn p := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
  have diff : ∀ j : Fin 5, fn (twoVotes j) ≠ fn (threeVotes j) := by decide +kernel
  exact ⟨_,_,diff i,fun q hq => by simp [threeVotes,hq]⟩

theorem supported_inputs : supported keys.toFinset fn := by
  intro x y eq
  apply congrArg vote
  funext i
  exact eq _ (List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨i,rfl⟩))

theorem mixed_listed {list f d} (h : Refined keys fn list f d) (k : Nat) :
    listed list f k ↔ 9+d ≤ k :=
  refined_listed h supported_inputs essential_input (p := (0,false)) (q := (1,false))
    (by decide) (by decide) (by decide) full_size k

def signedFor (list : List Coord) (f : Wire) (k : Nat) : Prop :=
  ∃ C : BinaryCircuit, (∀ g ∈ C.gates, FirstGate.parity g.op = false) ∧
    cost C ≤ k ∧ ∀ x : Row, C.eval (list.map x) = f x

theorem mixed_signed_lower {list f d} (h : Refined keys fn list f d) (k : Nat)
    (run : signedFor list f k) : 10+d ≤ k := by
  obtain ⟨C,hC,bd,ev⟩ := run
  have used := (refined_inputs h supported_inputs essential_input).2
  have nz := nonzero_of_essential (used (0,false) (refined_contains h (show (0,false) ∈ keys by decide)))
  have base (j : Nat) (b : FirstGate.bounded false keys fn j) : 10 ≤ j := root_lower false b
  exact (FirstGate.refined_lower h supported_inputs essential_input base (cost C)
    (FirstGate.of_circuit list f C (fun g hg => .inr (hC g hg)) ev nz)).trans bd

inductive Expanded : List Coord → Wire → Nat → Prop where
  | core : Expanded keys fn 0
  | step {list f d p q} (prev : Expanded list f d) (hp : p ∈ list) (hq : q ∉ list) (t : Bool) :
      Expanded (q::list) (split f t p q) (d+1)

theorem refined_of_expanded {list f d} (h : Expanded list f d) : Refined keys fn list f d := by
  induction h with
  | core => exact .start
  | step _ hp hq t prev =>
    exact .extend prev hp hq (join t) (by cases t <;> decide)

theorem nodup_inputs {list f d} (h : Expanded list f d) : list.Nodup := by
  induction h with
  | core => decide
  | step _ _ fresh _ prev => exact List.nodup_cons.mpr ⟨fresh,prev⟩

theorem monotone_upper {list f d} (h : Expanded list f d) : mono list f (10+d) := by
  induction h with
  | core => exact (monotone_size 10).mpr (by decide)
  | @step list f d p q prev hp _ t small => exact mono_split (nodup_inputs prev) hp q t small

theorem mono_to_signed {list f k} (h : mono list f k) : signedFor list f k := by
  obtain ⟨C,legal,bd,ev⟩ := h
  refine ⟨translate C,translated_parity C legal,?_,fun x => (translate_eval C (fun g hg => (legal g hg).2) _).trans (ev x)⟩
  exact (cost_le (translate C)).trans ((translate_size C) ▸ bd)

theorem expansion_sizes {list f d} (h : Expanded list f d) (k : Nat) :
    (listed list f k ↔ 9+d ≤ k) ∧ (signedFor list f k ↔ 10+d ≤ k) ∧ (mono list f k ↔ 10+d ≤ k) := by
  have refined := refined_of_expanded h
  have upper (bd : 10+d ≤ k) : mono list f k := by
    obtain ⟨C,legal,sm,ev⟩ := monotone_upper h
    exact ⟨C,legal,sm.trans bd,ev⟩
  exact ⟨mixed_listed refined k,⟨mixed_signed_lower refined k,fun b => mono_to_signed (upper b)⟩,
    ⟨fun r => mixed_signed_lower refined k (mono_to_signed r),upper⟩⟩

end FiveMajority
