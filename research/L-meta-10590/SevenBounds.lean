import PEqualNP.Outside.L_meta_9526

namespace SevenBounds

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_9526

def es : List ℕ := [0,2,1,3,0,4,2,4,0,5,1,5,2,5,3,5,0,6,1,6,2,6,3,6,5,6]

def target (x : Fin 7 → Bool) : Bool := decide (∃ i < es.length / 2,
  (List.ofFn x).getD (es.getD (2 * i) 0) false = true ∧
  (List.ofFn x).getD (es.getD (2 * i + 1) 0) false = true)

-- First six coordinates use the labels of the smaller graph, with vertex zero last.
def perm : Fin 7 → Fin 7 := ![6,3,0,4,5,1,2]

theorem unrestrictedLower (s : ℕ) (h : HasCircuitSize 7 target s) : 11 ≤ s := by
  let f : (Fin 7 → Bool) → Bool := fun x => target (x ∘ perm)
  have h' : HasCircuitSize 7 f s := remap_size perm target s h
  have dep : ∃ x : Fin 7 → Bool, f (Function.update x (Fin.last 6) (!x (Fin.last 6))) ≠ f x :=
    ⟨fun i => decide (i = 0), by decide +kernel⟩
  have nc : ∃ y y' : Fin 6 → Bool, f (Fin.snoc y false) ≠ f (Fin.snoc y' false) :=
    ⟨fun _ => false, fun _ => true, by decide +kernel⟩
  obtain ⟨s', pay, sub⟩ := gate_elim_one 6 f false s dep nc h'
  have eq : (fun y : Fin 6 → Bool => f (Fin.snoc y false)) = targetG := by
    funext y
    revert y
    decide +kernel
  rw [eq] at sub
  have := lb_G s' sub
  omega

def circuit : List Gate :=
  [⟨.or, [0,2]⟩, ⟨.or, [1,3]⟩, ⟨.or, [5,6]⟩,
   ⟨.and, [0,2]⟩, ⟨.and, [1,3]⟩, ⟨.and, [5,6]⟩,
   ⟨.and, [4,7]⟩, ⟨.or, [7,8]⟩, ⟨.and, [9,14]⟩,
   ⟨.or, [10,11]⟩, ⟨.or, [12,13]⟩, ⟨.or, [15,16]⟩, ⟨.or, [17,18]⟩]

theorem monotoneUpper : circuit.length = 13 ∧
    (∀ g ∈ circuit, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    ∀ x : Fin 7 → Bool, Circuit.eval ⟨circuit, 19⟩ (List.ofFn x) = target x := by
  refine ⟨rfl, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
  · decide +kernel

end SevenBounds
