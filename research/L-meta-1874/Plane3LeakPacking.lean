import PEqualNP.Defs

/-!
An extremal example for the packing condition in the checked reduction
R_meta_1874_721. A nonincident point-line pair accepted by one output is
called a leak. The two outputs below compute incidence when conjoined.
-/
namespace Plane3LeakPacking

open PEqualNP.HeptadCover

abbrev Index := Fin 13
abbrev Test := Index × Index

def leftLeaks (z m : Index) : Finset Test :=
  Finset.univ.filter fun e => e.1 ∉ singerLines3 e.2 ∧ e.1 ∈ singerLines3 m ∧ z ∈ singerLines3 e.2

def rightLeaks (z m : Index) : Finset Test :=
  Finset.univ.filter fun e => e.1 ∉ singerLines3 e.2 ∧ (e.1 = z ∨ e.2 = m)

theorem cross (z m : Index) {e f : Test} (he : e ∈ leftLeaks z m) (hf : f ∈ rightLeaks z m) :
    e.1 ∈ singerLines3 f.2 ∨ f.1 ∈ singerLines3 e.2 := by
  have left := (Finset.mem_filter.mp he).2
  rcases (Finset.mem_filter.mp hf).2.2 with h | h
  · exact Or.inr (h ▸ left.2.2)
  · exact Or.inl (h ▸ left.2.1)

theorem nonincident (z m : Index) {e : Test} (he : e ∈ leftLeaks z m ∪ rightLeaks z m) :
    e.1 ∉ singerLines3 e.2 := by
  rcases Finset.mem_union.mp he with h | h
  · exact (Finset.mem_filter.mp h).2.1
  · exact (Finset.mem_filter.mp h).2.1

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem sizes : ∀ z m : Index, z ∉ singerLines3 m →
    (leftLeaks z m).card = 12 ∧ (rightLeaks z m).card = 17 := by decide

def edge (P L : Finset Index) : Prop := ∃ p ∈ P, ∃ l ∈ L, p ∈ singerLines3 l

def outA (z m : Index) (P L : Finset Index) : Prop :=
  edge P L ∨ (∃ p ∈ P, p ∈ singerLines3 m) ∧ (∃ l ∈ L, z ∈ singerLines3 l)

def outB (z m : Index) (P L : Finset Index) : Prop :=
  edge P L ∨ z ∈ P ∨ m ∈ L

theorem conjunction (z m : Index) (P L : Finset Index) :
    outA z m P L ∧ outB z m P L ↔ edge P L := by
  constructor
  · rintro ⟨ha, hb⟩
    rcases ha with h | ⟨⟨p, hp, hpm⟩, ⟨l, hl, hzl⟩⟩
    · exact h
    rcases hb with h | hz | hm
    · exact h
    · exact ⟨z, hz, l, hl, hzl⟩
    · exact ⟨p, hp, m, hm, hpm⟩
  · exact fun h => ⟨Or.inl h, Or.inl h⟩

theorem leftSingleton (z m p l : Index) (h : p ∉ singerLines3 l) :
    outA z m {p} {l} ↔ (p, l) ∈ leftLeaks z m := by
  simp [outA, edge, leftLeaks, h]

theorem rightSingleton (z m p l : Index) (h : p ∉ singerLines3 l) :
    outB z m {p} {l} ↔ (p, l) ∈ rightLeaks z m := by
  simp [outB, edge, rightLeaks, h, eq_comm]

theorem sharpExample : ∃ A B : Finset Test,
    (∀ e ∈ A ∪ B, e.1 ∉ singerLines3 e.2) ∧
    (∀ e ∈ A, ∀ f ∈ B, e.1 ∈ singerLines3 f.2 ∨ f.1 ∈ singerLines3 e.2) ∧
    A.card = 12 ∧ B.card = 17 := by
  have counts := sizes 2 0 (by decide)
  exact ⟨leftLeaks 2 0, rightLeaks 2 0, fun _ h => nonincident 2 0 h,
    fun _ he _ hf => cross 2 0 he hf, counts⟩

theorem incomparableOnQuadrangles :
    (∃ Q, IsQuadrangle singerLines3 Q ∧
        outA 2 0 Q (missLines singerLines3 Q) ∧ ¬ outB 2 0 Q (missLines singerLines3 Q)) ∧
    (∃ Q, IsQuadrangle singerLines3 Q ∧
        outB 2 0 Q (missLines singerLines3 Q) ∧ ¬ outA 2 0 Q (missLines singerLines3 Q)) := by
  constructor
  · refine ⟨{0, 1, 4, 6}, ?_⟩
    unfold outA outB edge
    decide
  · refine ⟨{0, 1, 2, 5}, ?_⟩
    unfold outA outB edge
    decide

def flagsIn (P L : Finset Index) : Finset Test :=
  (P.product L).filter fun e => e.1 ∈ singerLines3 e.2

private theorem memFlags {P L : Finset Index} {e : Test} :
    e ∈ flagsIn P L ↔ (e.1 ∈ P ∧ e.2 ∈ L) ∧ e.1 ∈ singerLines3 e.2 := by
  simp [flagsIn, Finset.mem_product]

private theorem oneMeeting : ∀ m l : Index, m ≠ l →
    (singerLines3 m ∩ singerLines3 l).card ≤ 1 := by decide

private theorem samePoint {u v m l : Index} (ne : m ≠ l)
    (um : u ∈ singerLines3 m) (ul : u ∈ singerLines3 l)
    (vm : v ∈ singerLines3 m) (vl : v ∈ singerLines3 l) : u = v :=
  Finset.card_le_one.mp (oneMeeting m l ne) u (Finset.mem_inter.mpr ⟨um, ul⟩)
    v (Finset.mem_inter.mpr ⟨vm, vl⟩)

theorem collinearBound (P L : Finset Index) (m : Index) (hp : P ⊆ singerLines3 m) :
    (flagsIn P L).card ≤ P.card + L.card := by
  let E := flagsIn P L
  have central : (E.filter (fun e => e.2 = m)).card ≤ P.card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro e he
      exact (memFlags.mp (Finset.mem_filter.mp he).1).1.1
    · intro e he f hf eq
      exact Prod.ext eq ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm)
  have rest : (E.filter (fun e => e.2 ≠ m)).card ≤ L.card := by
    apply Finset.card_le_card_of_injOn Prod.snd
    · intro e he
      exact (memFlags.mp (Finset.mem_filter.mp he).1).1.2
    · intro e he f hf eq
      obtain ⟨⟨ep, _⟩, ei⟩ := memFlags.mp (Finset.mem_filter.mp he).1
      obtain ⟨⟨fp, _⟩, fi⟩ := memFlags.mp (Finset.mem_filter.mp hf).1
      have em : m ≠ e.2 := Ne.symm (Finset.mem_filter.mp he).2
      exact Prod.ext (samePoint em (hp ep) ei (hp fp) (eq ▸ fi)) eq
  have partition := Finset.card_filter_add_card_filter_not (s := E) (fun e => e.2 = m)
  change E.card ≤ _
  rw [← partition]
  exact Nat.add_le_add central rest

theorem concurrentBound (P L : Finset Index) (z : Index) (hl : ∀ l ∈ L, z ∈ singerLines3 l) :
    (flagsIn P L).card ≤ P.card + L.card := by
  let E := flagsIn P L
  have central : (E.filter (fun e => e.1 = z)).card ≤ L.card := by
    apply Finset.card_le_card_of_injOn Prod.snd
    · intro e he
      exact (memFlags.mp (Finset.mem_filter.mp he).1).1.2
    · intro e he f hf eq
      exact Prod.ext ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm) eq
  have rest : (E.filter (fun e => e.1 ≠ z)).card ≤ P.card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro e he
      exact (memFlags.mp (Finset.mem_filter.mp he).1).1.1
    · intro e he f hf eq
      obtain ⟨⟨_, el⟩, ei⟩ := memFlags.mp (Finset.mem_filter.mp he).1
      obtain ⟨⟨_, fl⟩, fi⟩ := memFlags.mp (Finset.mem_filter.mp hf).1
      apply Prod.ext eq
      by_contra ne
      have ez := samePoint ne ei (eq ▸ fi) (hl _ el) (hl _ fl)
      exact (Finset.mem_filter.mp he).2 ez
  have partition := Finset.card_filter_add_card_filter_not (s := E) (fun e => e.1 = z)
  change E.card ≤ _
  rw [← partition, Nat.add_comm P.card L.card]
  exact Nat.add_le_add central rest

-- All nonincident cells of an allowed rectangle lie in rows belonging to m.
theorem privateRectangleBound (P L : Finset Index) (m : Index)
    (allowed : ∀ p ∈ P, ∀ l ∈ L, p ∈ singerLines3 l ∨ p ∈ singerLines3 m) :
    (flagsIn P L).card ≤ P.card + L.card := by
  by_cases h : P ⊆ singerLines3 m
  · exact collinearBound P L m h
  obtain ⟨p, hp, hm⟩ := Finset.not_subset.mp h
  exact concurrentBound P L p (fun l hl => (allowed p hp l hl).resolve_right hm)

private def offsets : Finset Index := {0, 1, 3, 9}
private theorem flagDiff : ∀ p l : Index, p ∈ singerLines3 l → p-l ∈ offsets := by decide
private theorem diffLine : ∀ p l k : Index, p-l = p-k → l = k := by decide
private theorem diffPoint : ∀ p q l : Index, p-l = q-l → p = q := by decide
private theorem four : offsets.card = 4 := by decide

theorem pointCapacity (P L : Finset Index) : (flagsIn P L).card ≤ 4 * P.card := by
  have h : (flagsIn P L).card ≤ (P.product offsets).card := by
    apply Finset.card_le_card_of_injOn (fun e : Test => (e.1, e.1 - e.2))
    · intro e he
      have he' := memFlags.mp he
      exact Finset.mem_product.mpr ⟨he'.1.1, flagDiff _ _ he'.2⟩
    · rintro ⟨p,l⟩ _ ⟨q,k⟩ _ he
      obtain ⟨hp, hd⟩ := Prod.mk.inj he
      change p = q at hp
      change p - l = q - k at hd
      subst q
      exact Prod.ext rfl (diffLine _ _ _ hd)
  have eq : (P.product offsets).card = P.card * offsets.card := Finset.card_product _ _
  simpa only [eq, four, Nat.mul_comm P.card 4] using h

theorem lineCapacity (P L : Finset Index) : (flagsIn P L).card ≤ 4 * L.card := by
  have h : (flagsIn P L).card ≤ (L.product offsets).card := by
    apply Finset.card_le_card_of_injOn (fun e : Test => (e.2, e.1 - e.2))
    · intro e he
      have he' := memFlags.mp he
      exact Finset.mem_product.mpr ⟨he'.1.2, flagDiff _ _ he'.2⟩
    · rintro ⟨p,l⟩ _ ⟨q,k⟩ _ he
      obtain ⟨hl, hd⟩ := Prod.mk.inj he
      change l = k at hl
      change p - l = q - k at hd
      subst k
      exact Prod.ext (diffPoint _ _ _ hd) rfl
  have eq : (L.product offsets).card = L.card * offsets.card := Finset.card_product _ _
  simpa only [eq, four, Nat.mul_comm L.card 4] using h

theorem sharedRectangleBound (P L : Finset Index)
    (allowed : ∀ p ∈ P, ∀ l ∈ L, p ∈ singerLines3 l) :
    5 * (flagsIn P L).card ≤ 4 * (P.card + L.card) := by
  have pBound := pointCapacity P L
  have lBound := lineCapacity P L
  have sub : flagsIn P L ⊆ P.product L := Finset.filter_subset _ _
  have prodBound := Finset.card_le_card sub
  have eq : (P.product L).card = P.card * L.card := Finset.card_product _ _
  rw [eq] at prodBound
  by_cases pa : P.card ≤ 1
  · have := Nat.mul_le_mul_right L.card pa
    simp only [Nat.one_mul] at this
    by_cases zero : P.card = 0 <;> omega
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < P.card)
  have la : L.card ≤ 1 := Finset.card_le_one.mpr (by
    intro l hl k hk
    by_contra ne
    exact hpq (samePoint ne (allowed _ hp _ hl) (allowed _ hp _ hk)
      (allowed _ hq _ hl) (allowed _ hq _ hk)))
  have := Nat.mul_le_mul_left P.card la
  simp only [Nat.mul_one] at this
  by_cases zero : L.card = 0 <;> omega

abbrev Rectangle := Finset Index × Finset Index

def covered : List Rectangle → Finset Test
  | [] => ∅
  | r :: rs => flagsIn r.1 r.2 ∪ covered rs

def weight : List Rectangle → ℕ
  | [] => 0
  | r :: rs => (r.1.card + r.2.card) + weight rs

private theorem sumBound (rs : List Rectangle) (a b : ℕ)
    (h : ∀ r ∈ rs, a * (flagsIn r.1 r.2).card ≤ b * (r.1.card + r.2.card)) :
    a * (covered rs).card ≤ b * weight rs := by
  induction rs with
  | nil => simp [covered, weight]
  | cons r rs ih =>
    have tail := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    calc
      a * (covered (r :: rs)).card ≤
          a * ((flagsIn r.1 r.2).card + (covered rs).card) :=
        Nat.mul_le_mul_left _ (Finset.card_union_le _ _)
      _ = _ := Nat.mul_add a _ _
      _ ≤ b * (r.1.card + r.2.card) + b * weight rs :=
        Nat.add_le_add (h r List.mem_cons_self) tail
      _ = b * weight (r :: rs) := (Nat.mul_add b _ _).symm

-- The side weights charge shared rectangles once and private rectangles once
-- to their respective output. Point and line literals may also feed output B.
theorem twoOutputWeight (shared left right : List Rectangle) (m : Index)
    (pointLiterals lineLiterals : Finset Index)
    (hs : ∀ r ∈ shared, ∀ p ∈ r.1, ∀ l ∈ r.2, p ∈ singerLines3 l)
    (ha : ∀ r ∈ left, ∀ p ∈ r.1, ∀ l ∈ r.2, p ∈ singerLines3 l ∨ p ∈ singerLines3 m)
    (leftCovers : flagsIn Finset.univ Finset.univ ⊆ covered shared ∪ covered left)
    (rightCovers : flagsIn Finset.univ Finset.univ ⊆
      ((covered shared ∪ covered right) ∪ flagsIn pointLiterals Finset.univ)
        ∪ flagsIn Finset.univ lineLiterals) :
    65 ≤ weight shared + weight left + weight right + pointLiterals.card + lineLiterals.card := by
  have s := sumBound shared 5 4 (fun r hr => sharedRectangleBound _ _ (hs r hr))
  have a := sumBound left 1 1 (fun r hr => by
    simpa only [Nat.one_mul] using privateRectangleBound _ _ m (ha r hr))
  have b := sumBound right 1 4 (fun r _ => by
    simp only [Nat.one_mul]
    have := pointCapacity r.1 r.2
    omega)
  simp only [Nat.one_mul] at a b
  have pu := pointCapacity pointLiterals Finset.univ
  have lu := lineCapacity Finset.univ lineLiterals
  have cnt : (flagsIn Finset.univ Finset.univ).card = 52 := by decide
  have ac := Finset.card_le_card leftCovers
  have bc := Finset.card_le_card rightCovers
  rw [cnt] at ac bc
  have au := Finset.card_union_le (covered shared) (covered left)
  have bu := Finset.card_union_le (covered shared) (covered right)
  have bpu := Finset.card_union_le (covered shared ∪ covered right) (flagsIn pointLiterals Finset.univ)
  have blu := Finset.card_union_le
    ((covered shared ∪ covered right) ∪ flagsIn pointLiterals Finset.univ) (flagsIn Finset.univ lineLiterals)
  omega

end Plane3LeakPacking
