import CycleTable
import FullProjection
import SplitMonotone

namespace CycleCircuit
open Paired Paired.Split FullSearch LiveRestriction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def coord (i : Fin 5) : Coord := (i.val,false)
def keys := List.ofFn coord
def spec (x : Fin 5 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0)
def fn (x : Row) : Bool := spec (fun i => x (coord i))
def rows : Samples := fun i p => (FullSearch.Cycle.samples[i.val]?.getD 0).testBit p.1

theorem nonzero : normalize fn ≠ Paired.zero := by
  intro e
  have h := congrFun e (fun _ => true)
  exact Bool.noConfusion (show true = false from h)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem input_words : ∀ i : Fin 5, pack rows (input (coord i)) ∈ FullSearch.Cycle.inputs := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem goal_word : pack rows (normalize fn) = FullSearch.goal := by decide +kernel

theorem lower {k : ℕ} (h : native keys fn k) : 7 ≤ k := by
  classical
  have run := (native_iff keys fn k nonzero).mp h
  have cover : project (pack rows) 0 (primaryBank keys.toFinset) ⊆ FullSearch.Cycle.inputs.toFinset := by
    intro w hw
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hw).2
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hp)
    exact List.mem_toFinset.mpr (input_words i)
  exact packed_bound (by decide +kernel) FullSearch.Cycle.excluded goal_word cover run
    (saved := 0) (fun _ _ _ => Nat.zero_le _)

def gates : List Gate :=
  [⟨.or,[1,4]⟩,⟨.and,[0,5]⟩,⟨.or,[1,3]⟩,⟨.and,[2,7]⟩,⟨.and,[3,4]⟩,⟨.or,[6,8]⟩,⟨.or,[10,9]⟩]
def circuit : Circuit := ⟨gates,11⟩

theorem upper : mono keys fn 7 := by
  have ok : Monotone2 circuit := by
    intro g hg
    simp only [circuit,gates,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have eval : ∀ x : Fin 5 → Bool, circuit.eval (List.ofFn x) = spec x := by decide +kernel
  refine ⟨circuit,ok,by decide,?_⟩
  intro x
  simpa [keys,fn] using eval (fun i => x (coord i))

theorem exact_size (k : ℕ) : native keys fn k ↔ 7 ≤ k := by
  refine ⟨lower,?_⟩
  intro le
  obtain ⟨C,ok,bd,ev⟩ := upper
  refine ⟨translate C,?_,fun x => (translate_eval _ (fun g hg => (ok g hg).2) _).trans (ev x)⟩
  have cost := cost_le (translate C)
  rw [translate_size] at cost
  omega

end CycleCircuit
