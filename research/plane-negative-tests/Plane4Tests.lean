import SmallAnd

namespace Plane4Tests
open SmallAnd PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev V := Fin 42
def seed : List Nat := [0,1,2,6,8,18,24,31,33,37]
def move (k p : V) : V :=
  ⟨(if k.val < 21 then (p.val+k.val)%21 else (k.val+42-p.val)%21) +
   (if (p.val<21) = (k.val<21) then 0 else 21),by split_ifs <;> omega⟩
def pull (k p : V) : V :=
  ⟨(if k.val < 21 then (p.val+21-k.val)%21 else (k.val+42-p.val)%21) +
   (if (p.val<21) = (k.val<21) then 0 else 21),by split_ifs <;> omega⟩
def test (k p : V) := seed.contains (pull k p).val
def flag (u v : V) : Bool := decide (u.val < 21 ∧ 21 ≤ v.val) &&
  [0,5,7,17,20].contains ((v.val + 21 - u.val) % 21)
def set (k : V) : Finset V := Finset.univ.filter fun p => test k p = true
def Negative (S : Finset V) : Prop := ∀ u ∈ S, ∀ v ∈ S, flag u v = false

def check2 (p : V → V → Bool) := (List.finRange 42).all fun a => (List.finRange 42).all (p a)
def check3 (p : V → V → V → Bool) := (List.finRange 42).all fun a => check2 (p a)
theorem run2 {p : V → V → Bool} (h : check2 p = true) (a b : V) : p a b = true := by
  exact List.all_eq_true.mp (List.all_eq_true.mp h a (by simp)) b (by simp)
theorem run3 {p : V → V → V → Bool} (h : check3 p = true) (a b c : V) : p a b c = true := by
  exact run2 (List.all_eq_true.mp h a (by simp)) b c

set_option maxHeartbeats 0 in
theorem permutes (k p : V) : pull k (move k p) = p ∧ move k (pull k p) = p := by
  have h : check2 (fun i j => decide (pull i (move i j)=j ∧ move i (pull i j)=j)) = true := by decide +kernel
  exact of_decide_eq_true (run2 h k p)
set_option maxHeartbeats 0 in
theorem immutable (k u v : V) : (flag (move k u) (move k v) || flag (move k v) (move k u)) =
    (flag u v || flag v u) := by
  have h : check3 (fun a b c => (flag (move a b) (move a c) || flag (move a c) (move a b)) ==
    (flag b c || flag c b)) = true := by decide +kernel
  exact beq_iff_eq.mp (run3 h k u v)
set_option maxHeartbeats 0 in
theorem seed_negative (u v : V) (su : seed.contains u.val) (sv : seed.contains v.val) : flag u v = false := by
  have h : check2 (fun a b => !(seed.contains a.val && seed.contains b.val && flag a b)) = true := by decide +kernel
  have z := run2 h u v
  change !(seed.contains u.val && seed.contains v.val && flag u v) = true at z
  rw [su,sv] at z
  simpa using z
set_option maxHeartbeats 0 in
theorem pair_covered (u v : V) (h1 : flag u v = false) (h2 : flag v u = false) :
    ∃ k : V, test k u = true ∧ test k v = true := by
  have h : check2 (fun a b => (flag a b || flag b a) || (List.finRange 42).any (fun k => test k a && test k b)) = true := by decide +kernel
  simpa [h1,h2] using run2 h u v
set_option maxHeartbeats 0 in
theorem private_pair (k j : V) : (test j (move k 0) && test j (move k 18)) = decide (k=j) := by
  have h : check2 (fun a b => (test b (move a 0) && test b (move a 18)) == decide (a=b)) = true := by decide +kernel
  exact beq_iff_eq.mp (run2 h k j)


theorem valid (k : V) : Negative (set k) := by
  intro u hu v hv
  have su : seed.contains (pull k u).val = true := (Finset.mem_filter.mp hu).2
  have sv : seed.contains (pull k v).val = true := (Finset.mem_filter.mp hv).2
  have eq := immutable k (pull k u) (pull k v)
  rw [(permutes k u).2,(permutes k v).2,seed_negative _ _ su sv,seed_negative _ _ sv su] at eq
  cases e : flag u v <;> simp_all

theorem cover (T : Finset V) (neg : Negative T) (card : T.card ≤ 2) : ∃ k : V, T ⊆ set k := by
  apply cover_pairs set T card
  intro a ha b hb
  obtain ⟨k,x,y⟩ := pair_covered a b (neg a ha b hb) (neg b hb a ha)
  exact ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,x⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,y⟩⟩

theorem certify (C : Circuit) (mono : Monotone2 C) :
    (∃ S, Negative S ∧ Active C.gates S) ↔ ∃ k : V, Active C.gates (set k) := by
  constructor
  · rintro ⟨S,neg,act⟩
    obtain ⟨T,sub,bd,yes⟩ := sparse C mono S act
    obtain ⟨k,ext⟩ := cover T (fun u hu v hv => neg u (sub hu) v (sub hv)) bd
    exact ⟨k,mono_active C mono ext yes⟩
  · rintro ⟨k,yes⟩
    exact ⟨set k,valid k,yes⟩
end Plane4Tests
