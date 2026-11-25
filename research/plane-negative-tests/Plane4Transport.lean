import Plane4Tests
import PEqualNP.MetaComplexity.Helpers.PermInputs

namespace Plane4Tests
open SmallAnd PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.PermInputs

def Positive (x : V → Bool) : Prop := ∃ u v : V, (flag u v || flag v u) = true ∧ x u = true ∧ x v = true
def Correct (C : Circuit) := ∀ x : V → Bool, C.eval (List.ofFn x) = true ↔ Positive x
def seedSet : Finset V := Finset.univ.filter fun v => seed.contains v.val = true

theorem positive_pull (k : V) (x : V → Bool) : Positive (x ∘ pull k) ↔ Positive x := by
  constructor
  · rintro ⟨u,v,h,hu,hv⟩
    refine ⟨pull k u,pull k v,?_,hu,hv⟩
    have eq := immutable k (pull k u) (pull k v)
    simpa only [(permutes k u).2,(permutes k v).2,h] using eq.symm
  · rintro ⟨u,v,h,hu,hv⟩
    exact ⟨move k u,move k v,(immutable k u v).trans h,by simpa [Function.comp_apply,(permutes k u).1],by simpa [Function.comp_apply,(permutes k v).1]⟩

theorem transport (C : Circuit) (mono : Monotone2 C) (correct : Correct C) (k : V)
    (active : Active C.gates (set k)) :
    ∃ D : Circuit, D.size=C.size ∧ Monotone2 D ∧ Correct D ∧ Active D.gates seedSet := by
  let π := pull k
  let D := relabel 42 42 π C
  refine ⟨D,by simp [D,relabel,Circuit.size],?_,?_,?_⟩
  · intro g hg
    obtain ⟨old,mem,rfl⟩ := List.mem_map.mp hg
    exact ⟨(mono old mem).1,by simpa [relGate] using (mono old mem).2⟩
  · intro x
    have eq := (rel_fold 42 42 π C.gates _ _ (rel_init 42 42 π x)).2.2 C.output
    change D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ π)) at eq
    rw [eq,correct]
    exact positive_pull k x
  · obtain ⟨j,g,atj,op,yes⟩ := active
    refine ⟨j,relGate 42 42 π g,?_,op,?_⟩
    · simp [D,relabel,List.getElem?_map,atj]
    · let x : V → Bool := fun v => decide (v ∈ seedSet)
      have eq := (rel_fold 42 42 π C.gates _ _ (rel_init 42 42 π x)).2.2 (42+j)
      have ew : wmap 42 42 π (42+j) = 42+j := by simp [wmap]; omega
      rw [ew] at eq
      have inp : (x ∘ π) = fun v => decide (v ∈ set k) := by
        funext v
        simp [x,π,seedSet,set,test,Function.comp_apply]
      rw [inp] at eq
      exact eq.trans yes

set_option maxHeartbeats 0 in
theorem set_zero : set 0 = seedSet := by decide +kernel

theorem dirty_equivalence (size : Nat) :
    (∃ C : Circuit, C.size ≤ size ∧ Monotone2 C ∧ Correct C ∧ ∃ S, Negative S ∧ Active C.gates S) ↔
    (∃ C : Circuit, C.size ≤ size ∧ Monotone2 C ∧ Correct C ∧ Active C.gates seedSet) := by
  constructor
  · rintro ⟨C,bd,mono,correct,dirty⟩
    obtain ⟨k,active⟩ := (certify C mono).mp dirty
    obtain ⟨D,e,m,c,a⟩ := transport C mono correct k active
    exact ⟨D,e.le.trans bd,m,c,a⟩
  · rintro ⟨C,bd,mono,correct,active⟩
    exact ⟨C,bd,mono,correct,seedSet,by rw [← set_zero]; exact valid 0,active⟩

end Plane4Tests
