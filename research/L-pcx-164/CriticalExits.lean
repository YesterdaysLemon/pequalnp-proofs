import PEqualNP.Defs

namespace CriticalExits
open PEqualNP.ProofComplexity

-- Record an upper bound S for the distinct clauses reached when a chosen
-- axiom A is used as a resolution parent. A copy of A may be ignored.
inductive Trace {V : Type} [DecidableEq V] (F : Set (Clause V)) (A : Clause V)
    (S : Finset (Clause V)) : List (Clause V) → Prop
  | nil : Trace F A S []
  | ax {π C} : Trace F A S π → C ∈ F → Trace F A S (C :: π)
  | res {π C D R} : Trace F A S π → C ∈ π → D ∈ π → IsResolvent C D R →
      (R ≠ A → C = A ∨ D = A → R ∈ S) → Trace F A S (R :: π)

theorem Trace.forget {V} [DecidableEq V] {F : Set (Clause V)} {A S π}
    (h : Trace F A S π) : IsDerivation F π := by
  induction h with
  | nil => exact .nil
  | ax _ h ih => exact .ax ih h
  | res _ hc hd hr _ ih => exact .res ih hc hd hr

theorem badParent {V} [DecidableEq V] (a : V → Bool) {C D R : Clause V}
    (hr : IsResolvent C D R) (h : ¬ClauseSat a R) : ¬ClauseSat a C ∨ ¬ClauseSat a D := by
  obtain ⟨v,hv,hw,rfl⟩ := hr
  cases val : a v with
  | false =>
    left
    rintro ⟨q,hq,hval⟩
    exact h ⟨q,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by
      rintro rfl
      simp [val] at hval,hq⟩),hval⟩
  | true =>
    right
    rintro ⟨q,hq,hval⟩
    exact h ⟨q,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨by
      rintro rfl
      simp [val] at hval,hq⟩),hval⟩

theorem exit {V} [DecidableEq V] {F : Set (Clause V)} {A S π}
    (h : Trace F A S π) (a : V → Bool) (critical : ∀ C ∈ F, C ≠ A → ClauseSat a C)
    {Q} (hq : Q ∈ π) (hne : Q ≠ A) (hf : ¬ClauseSat a Q) :
    ∃ R ∈ S, ¬ClauseSat a R := by
  induction h generalizing Q with
  | nil => simp at hq
  | @ax π C tr ha ih =>
    rcases List.mem_cons.mp hq with rfl | ht
    · exact (hf (critical _ ha hne)).elim
    · exact ih ht hne hf
  | @res π C D R tr hc hd hr hs ih =>
    rcases List.mem_cons.mp hq with rfl | ht
    · rcases badParent a hr hf with h1 | h2
      · by_cases eq : C = A
        · exact ⟨_, hs hne (Or.inl eq), hf⟩
        · exact ih hc eq h1
      · by_cases eq : D = A
        · exact ⟨_, hs hne (Or.inr eq), hf⟩
        · exact ih hd eq h2
    · exact ih ht hne hf

def assignment {n} (bits : ℕ) : Fin (n+1) × Fin n → Bool := fun v =>
  bits.testBit (n*v.1.val+v.2.val)

abbrev V := Fin 5 × Fin 4
def row (p : Fin 5) : Clause V := Finset.univ.image (fun h : Fin 4 => ((p,h),true))
def collision (p q : Fin 5) (h : Fin 4) : Clause V := {((p,h),false),((q,h),false)}

-- Each permutation of the other pigeons gives one collision-critical input.
-- A third negative literal is false on at most two of these six inputs.
def six : Fin 6 → ℕ := ![541201,295441,533521,164881,272401,149521]

def pigeonBits : Fin 24 → ℕ := ![541200,295440,533520,164880,272400,149520,
  540960,295200,529440,99360,268320,84000,532800,164160,528960,98880,137280,
  75840,270720,147840,266880,82560,136320,74880]

def colSample (k : Fin 6) : V → Bool := assignment (six k)
def rowSample (k : Fin 24) : V → Bool := assignment (pigeonBits k)
def positives {k} (sample : Fin k → V → Bool) (v : V) : Finset (Fin k) :=
  Finset.univ.filter fun i => sample i v = true

theorem colRows : ∀ k (p : Fin 5), ∃ l : Fin 4, colSample k (p,l) = true := by decide
theorem colCollisions : ∀ k (p q : Fin 5) (l : Fin 4), p ≠ q →
    colSample k (p,l) = true → colSample k (q,l) = true →
      ((p=0 ∧ q=1) ∨ (p=1 ∧ q=0)) ∧ l=0 := by decide
theorem rowRows : ∀ k (p : Fin 5), p ≠ 0 → ∃ l : Fin 4, rowSample k (p,l) = true := by decide
theorem rowCollisions : ∀ k (p q : Fin 5) (l : Fin 4), p ≠ q →
    rowSample k (p,l) = true → rowSample k (q,l) = false := by decide
theorem colBias : ∀ v : V, v ≠ (0,0) → v ≠ (1,0) → (positives colSample v).card ≤ 2 := by decide
theorem rowBias : ∀ v : V, (positives rowSample v).card ≤ 6 := by decide

theorem colCritical (i : Fin 6) : ∀ C ∈ PHP 5 4, C ≠ collision 0 1 0 → ClauseSat (colSample i) C := by
  rintro C (⟨p,rfl⟩ | ⟨p,q,l,hpq,rfl⟩) ne
  · obtain ⟨l,hl⟩ := colRows i p
    exact ⟨_,Finset.mem_image.mpr ⟨l,Finset.mem_univ _,rfl⟩,hl⟩
  · cases h : colSample i (p,l)
    · exact ⟨_,Finset.mem_insert_self ..,h⟩
    cases h' : colSample i (q,l)
    · exact ⟨((q,l),false),by simp,h'⟩
    obtain ⟨hpair,rfl⟩ := colCollisions i p q l hpq h h'
    rcases hpair with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact (ne rfl).elim
    · exact (ne (by simp [collision, Finset.pair_comm])).elim

theorem rowCritical (i : Fin 24) : ∀ C ∈ PHP 5 4, C ≠ row 0 → ClauseSat (rowSample i) C := by
  rintro C (⟨p,rfl⟩ | ⟨p,q,l,hpq,rfl⟩) ne
  · have hn : p ≠ 0 := by rintro rfl; exact ne rfl
    obtain ⟨l,hl⟩ := rowRows i p hn
    exact ⟨_,Finset.mem_image.mpr ⟨l,Finset.mem_univ _,rfl⟩,hl⟩
  · cases h : rowSample i (p,l)
    · exact ⟨_,Finset.mem_insert_self ..,h⟩
    · exact ⟨((q,l),false),by simp,rowCollisions i p q l hpq h⟩

theorem cost {k b} (sample : Fin k → V → Bool) {F : Set (Clause V)} {A S π}
    (critical : ∀ i, ∀ C ∈ F, C ≠ A → ClauseSat (sample i) C)
    (trace : Trace F A S π) (empty : (∅ : Clause V) ∈ π) (ne : (∅ : Clause V) ≠ A)
    (neg : ∀ C ∈ S, ∃ v, (v,false) ∈ C ∧ (positives sample v).card ≤ b) : k ≤ S.card * b := by
  classical
  let miss := fun C : Clause V => Finset.univ.filter (fun i : Fin k => ¬ClauseSat (sample i) C)
  have hsub : Finset.univ ⊆ S.biUnion miss := by
    intro i _
    obtain ⟨R,hR,hm⟩ := exit trace (sample i) (critical i) empty ne (by simp [ClauseSat])
    exact Finset.mem_biUnion.mpr ⟨R,hR,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm⟩⟩
  have hcap (C) (hC : C ∈ S) : (miss C).card ≤ b := by
    obtain ⟨v,hv,hb⟩ := neg C hC
    apply le_trans (Finset.card_le_card (s := miss C) (t := positives sample v) ?_) hb
    intro i hi
    obtain ⟨_,h⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    cases hh : sample i v
    · exact (h ⟨_,hv,hh⟩).elim
    · rfl
  calc
    k = (Finset.univ : Finset (Fin k)).card := by simp
    _ ≤ (S.biUnion miss).card := Finset.card_le_card hsub
    _ ≤ ∑ C ∈ S, (miss C).card := Finset.card_biUnion_le
    _ ≤ ∑ _C ∈ S, b := Finset.sum_le_sum hcap
    _ = S.card * b := by simp

theorem threeCollisionExits {S π} (trace : Trace (PHP 5 4) (collision 0 1 0) S π)
    (empty : (∅ : Clause V) ∈ π)
    (external : ∀ C ∈ S, ∃ v : V, (v,false) ∈ C ∧ v ≠ (0,0) ∧ v ≠ (1,0)) :
    3 ≤ S.card := by
  have hn : (∅ : Clause V) ≠ collision 0 1 0 := by decide
  have bound := cost (b:=2) colSample colCritical trace empty hn (fun C hC => by
    obtain ⟨v,hv,h0,h1⟩ := external C hC
    exact ⟨v,hv,colBias v h0 h1⟩)
  omega

theorem fourPigeonExits {S π} (trace : Trace (PHP 5 4) (row 0) S π)
    (empty : (∅ : Clause V) ∈ π) (negative : ∀ C ∈ S, ∃ v : V, (v,false) ∈ C) :
    4 ≤ S.card := by
  have hn : (∅ : Clause V) ≠ row 0 := by decide
  have bound := cost (b:=6) rowSample rowCritical trace empty hn (fun C hC => by
    obtain ⟨v,hv⟩ := negative C hC
    exact ⟨v,hv,rowBias v⟩)
  omega

theorem pairPerm (p q : Fin 5) (hne : p ≠ q) :
    ∃ r : Fin 5 ≃ Fin 5, r p = 0 ∧ r q = 1 := by
  let a := Equiv.swap p 0
  have hp : a p = 0 := Equiv.swap_apply_left ..
  have hn : a q ≠ 0 := fun h => hne (a.injective (hp.trans h.symm))
  refine ⟨a.trans (Equiv.swap (a q) 1),?_,?_⟩
  · change Equiv.swap (a q) 1 (a p) = 0
    rw [hp]
    exact Equiv.swap_apply_of_ne_of_ne hn.symm (by decide)
  · exact Equiv.swap_apply_left ..

theorem collisionBound (p0 q0 : Fin 5) (l0 : Fin 4) (pq : p0 ≠ q0) {S π}
    (trace : Trace (PHP 5 4) (collision p0 q0 l0) S π) (empty : (∅ : Clause V) ∈ π)
    (external : ∀ C ∈ S, ∃ v : V, (v,false) ∈ C ∧ v ≠ (p0,l0) ∧ v ≠ (q0,l0)) :
    3 ≤ S.card := by
  obtain ⟨r,hp,hq⟩ := pairPerm p0 q0 pq
  let s := Equiv.swap l0 0
  have hl : s l0 = 0 := Equiv.swap_apply_left ..
  let sample (i : Fin 6) (v : V) := colSample i (r v.1,s v.2)
  have ne : (∅ : Clause V) ≠ collision p0 q0 l0 := by
    intro h
    have hm : ((p0,l0),false) ∈ collision p0 q0 l0 := Finset.mem_insert_self ..
    rw [← h] at hm
    exact Finset.notMem_empty _ hm
  have crit (i : Fin 6) : ∀ C ∈ PHP 5 4, C ≠ collision p0 q0 l0 → ClauseSat (sample i) C := by
    rintro C (⟨p,rfl⟩ | ⟨p,q,l,hpq,rfl⟩) hne
    · obtain ⟨h,hv⟩ := colRows i (r p)
      refine ⟨((p,s.symm h),true),Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩,?_⟩
      simpa [sample] using hv
    · cases h : sample i (p,l)
      · exact ⟨_,Finset.mem_insert_self ..,h⟩
      cases h' : sample i (q,l)
      · exact ⟨((q,l),false),by simp,h'⟩
      obtain ⟨hpq',hl'⟩ := colCollisions i (r p) (r q) (s l) (fun e => hpq (r.injective e)) h h'
      have el : l = l0 := s.injective (hl'.trans hl.symm)
      rcases hpq' with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · exact (hne (by rw [r.injective (ha.trans hp.symm),r.injective (hb.trans hq.symm),el]; rfl)).elim
      · exact (hne (by rw [r.injective (ha.trans hq.symm),r.injective (hb.trans hp.symm),el]
                       simp [collision,Finset.pair_comm])).elim
  have bound := cost (b:=2) sample crit trace empty ne (fun C hC => by
    obtain ⟨v,hv,h1,h2⟩ := external C hC
    refine ⟨v,hv,colBias (r v.1,s v.2) ?_ ?_⟩
    · intro e
      exact h1 (Prod.ext (r.injective ((congrArg Prod.fst e).trans hp.symm))
        (s.injective ((congrArg Prod.snd e).trans hl.symm)))
    · intro e
      exact h2 (Prod.ext (r.injective ((congrArg Prod.fst e).trans hq.symm))
        (s.injective ((congrArg Prod.snd e).trans hl.symm))))
  omega

theorem pigeonBound (p0 : Fin 5) {S π} (trace : Trace (PHP 5 4) (row p0) S π)
    (empty : (∅ : Clause V) ∈ π) (negative : ∀ C ∈ S, ∃ v : V, (v,false) ∈ C) :
    4 ≤ S.card := by
  let r := Equiv.swap p0 0
  have hp : r p0 = 0 := Equiv.swap_apply_left ..
  let sample (i : Fin 24) (v : V) := rowSample i (r v.1,v.2)
  have ne : (∅ : Clause V) ≠ row p0 := by
    intro h
    have hm : ((p0,(0 : Fin 4)),true) ∈ row p0 := Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩
    rw [← h] at hm
    exact Finset.notMem_empty _ hm
  have crit (i : Fin 24) : ∀ C ∈ PHP 5 4, C ≠ row p0 → ClauseSat (sample i) C := by
    rintro C (⟨p,rfl⟩ | ⟨p,q,l,hpq,rfl⟩) hne
    · have hn : r p ≠ 0 := by intro h; exact hne (by rw [r.injective (h.trans hp.symm)]; rfl)
      obtain ⟨h,hv⟩ := rowRows i (r p) hn
      exact ⟨_,Finset.mem_image.mpr ⟨h,Finset.mem_univ _,rfl⟩,hv⟩
    · cases h : sample i (p,l)
      · exact ⟨_,Finset.mem_insert_self ..,h⟩
      · exact ⟨((q,l),false),by simp,rowCollisions i _ _ l (fun e => hpq (r.injective e)) h⟩
  have bound := cost (b:=6) sample crit trace empty ne (fun C hC => by
    obtain ⟨v,hv⟩ := negative C hC
    exact ⟨v,hv,rowBias (r v.1,v.2)⟩)
  omega

end CriticalExits
