import ThresholdFour
import MajorityCombinatorics

namespace FiveMajority
open Paired Paired.Split FullSearch LiveRestriction

def samples (p : Fin 5) (b : Bool) : Samples := fun j v =>
  if v.1 = p.val then b else
    ((ThresholdFour.rows[j.val]?.getD 0).testBit (if v.1 < p.val then v.1 else v.1-1)) ^^ b

theorem pin_at (p : Fin 5) (b : Bool) (j : Fin 512) : samples p b j (coord p) = b := by
  simp [samples,coord]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem goal_word : ∀ (p : Fin 5) (b : Bool), pack (samples p b) (normalize fn) = goal := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem small_words : ∀ (p i : Fin 5) (b : Bool), pack (samples p b) (input (coord i)) = 0 ∨
    pack (samples p b) (input (coord i)) ∈ ThresholdFour.inputs := by decide +kernel

theorem lost_pin (p : Fin 5) (b : Bool) : pack (samples p b) (input (coord p)) = 0 := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  change (pack (samples p b) (input (coord p)))[(⟨i,hi⟩ : Fin 512).val] = _
  rw [pack_at]
  simp [input,pin_at]

theorem lost_gate {i j : Fin 5} {o : Op} {b : Bool} (h : ∀ t, o b t = o b false) :
    pack (samples i b) (combine o (input (coord i)) (input (coord j))) = 0 := by
  apply BitVec.eq_of_getElem_eq
  intro l hl
  change (pack (samples i b) (combine o (input (coord i)) (input (coord j))))[(⟨l,hl⟩ : Fin 512).val] = _
  rw [pack_at]
  simp [combine,input,pin_at,h]

theorem coord_injective : Function.Injective coord := fun _ _ h => Fin.ext (congrArg Prod.fst h)
theorem nonzero : normalize fn ≠ Paired.zero := by
  intro e; exact Bool.noConfusion (congrFun e (fun _ => true))

end FiveMajority
