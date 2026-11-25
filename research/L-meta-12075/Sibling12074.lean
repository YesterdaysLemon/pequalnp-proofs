import BlockFamily

namespace Sibling12074
open PEqualNP.Outside.L_meta_12072
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4269860864 * 2 ^ 32 + 4269801472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def circuit : List Gate := [⟨.and,[1,0]⟩, ⟨.or,[1,0]⟩, ⟨.and,[3,2]⟩, ⟨.and,[4,2]⟩, ⟨.and,[7,3]⟩, ⟨.or,[8,6]⟩, ⟨.and,[10,4]⟩, ⟨.and,[10,5]⟩, ⟨.or,[13,9]⟩, ⟨.and,[14,11]⟩, ⟨.or,[15,12]⟩]

theorem monotoneUpper : Monotone2 ⟨circuit,16⟩ ∧
    ∀ x : Fin 6 → Bool, Circuit.eval ⟨circuit,16⟩ (List.ofFn x) = target x := by
  refine ⟨?_, ?_⟩
  · intro g hg
    change g ∈ circuit at hg
    change (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2
    simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
  · decide +kernel
theorem comparison (s : ℕ) (h : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  apply SharedBlock.comparison target 0x8000fe008000fee8 3 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) _ s h
  exact ⟨⟨circuit,16⟩,monotoneUpper.1,by decide,monotoneUpper.2⟩

end Sibling12074

example :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269860864 * 2 ^ 32 + 4269801472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269860864 * 2 ^ 32 + 4269801472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := Sibling12074.comparison
