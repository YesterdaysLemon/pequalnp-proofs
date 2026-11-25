import Plane4Tests

namespace Plane4Compact
open SmallAnd Plane4Tests PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev I := Fin 17
def masks : Array Nat := #[2234602101024,300818139660,1514051510674,757025755337,664110497877,1194139585049,20754829314,2358476801188,562671142657,281761358336,2097151,2551277701142,1138535638026,3848575977056,4398044413952,378513926244,550762692624]
def included (i : I) (v : V) := (masks[i.val]?.getD 0).testBit v.val
def sample (i : I) : Finset V := Finset.univ.filter fun v => included i v = true

set_option maxHeartbeats 0 in
theorem samples_negative (i : I) : Negative (sample i) := by
  intro u hu v hv
  have h : (List.finRange 17).all (fun a => check2 (fun b c => !(included a b && included a c && flag b c))) = true := by decide +kernel
  have z := run2 (List.all_eq_true.mp h i (by simp)) u v
  change !(included i u && included i v && flag u v) = true at z
  rw [(Finset.mem_filter.mp hu).2,(Finset.mem_filter.mp hv).2] at z
  simpa using z

set_option maxHeartbeats 0 in
theorem samples_cover (u v : V) (h1 : flag u v = false) (h2 : flag v u = false) :
    ∃ i : I, included i u = true ∧ included i v = true := by
  have h : check2 (fun a b => (flag a b || flag b a) ||
    (List.finRange 17).any (fun i => included i a && included i b)) = true := by decide +kernel
  simpa [h1,h2] using run2 h u v

theorem certified (C : Circuit) (mono : Monotone2 C) :
    (∃ S, Negative S ∧ Active C.gates S) ↔ ∃ i : I, Active C.gates (sample i) := by
  constructor
  · rintro ⟨S,neg,act⟩
    obtain ⟨T,sub,bd,yes⟩ := sparse C mono S act
    have pairs : ∀ a ∈ T, ∀ b ∈ T, ∃ i, a ∈ sample i ∧ b ∈ sample i := by
      intro a ha b hb
      obtain ⟨i,x,y⟩ := samples_cover a b (neg a (sub ha) b (sub hb)) (neg b (sub hb) a (sub ha))
      exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,x⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,y⟩⟩
    obtain ⟨i,ext⟩ := cover_pairs sample T bd pairs
    exact ⟨i,mono_active C mono ext yes⟩
  · rintro ⟨i,yes⟩
    exact ⟨sample i,samples_negative i,yes⟩
end Plane4Compact
