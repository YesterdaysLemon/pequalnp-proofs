import PEqualNP.Defs

/-!
The incidence relation of L-meta-4197. A rectangle is the product of a set
of points and a set of lines. The weight of a list of rectangles is the sum
of all its side sizes, with repetitions counted.

For nonempty sides, a binary formula that computes the two side disjunctions
of every rectangle independently, ANDs each pair, and ORs the results has one
fewer gate than this weight. The sharp bound below concerns those formulas.
-/
namespace Plane4RectangleCover

abbrev Index := Fin 21
abbrev Rectangle := Finset Index × Finset Index

def incident (p l : Index) : Bool :=
  decide (p = l ∨ p = l + 1 ∨ p = l + 4 ∨ p = l + 14 ∨ p = l + 16)

def linesThrough (p : Index) : Finset Index := Finset.univ.filter (incident p ·)
def pointsOn (l : Index) : Finset Index := Finset.univ.filter (incident · l)
def flags : Finset (Index × Index) := Finset.univ.filter fun e => incident e.1 e.2

def valid (r : Rectangle) : Prop := ∀ p ∈ r.1, ∀ l ∈ r.2, incident p l = true

def covered : List Rectangle → Finset (Index × Index)
  | [] => ∅
  | r :: rs => r.1.product r.2 ∪ covered rs

def weight : List Rectangle → ℕ
  | [] => 0
  | r :: rs => r.1.card + r.2.card + weight rs

private theorem degreeP : ∀ p, (linesThrough p).card = 5 := by decide
private theorem degreeL : ∀ l, (pointsOn l).card = 5 := by decide
private theorem numberOfFlags : flags.card = 105 := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem oneCommon : ∀ p q : Index, p ≠ q →
    (linesThrough p ∩ linesThrough q).card ≤ 1 := by decide

theorem uniqueLineForSum (s : Finset Index) (hs : 1 < s.card) {l k : Index}
    (hl : s ⊆ pointsOn l) (hk : s ⊆ pointsOn k) : l = k := by
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hs
  have both (v : Index) (hv : s ⊆ pointsOn v) : v ∈ linesThrough p ∩ linesThrough q := by
    apply Finset.mem_inter.mpr
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp (hv hp)).2⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp (hv hq)).2⟩⟩
  exact (Finset.card_le_one.mp (oneCommon p q hpq)) l (both l hl) k (both k hk)

theorem uniquePointForSum (s : Finset Index) (hs : 1 < s.card) {p q : Index}
    (hp : s ⊆ linesThrough p) (hq : s ⊆ linesThrough q) : p = q := by
  by_contra ne
  have sub : s ⊆ linesThrough p ∩ linesThrough q :=
    fun x hx => Finset.mem_inter.mpr ⟨hp hx, hq hx⟩
  exact (Nat.not_le_of_gt hs) ((Finset.card_le_card sub).trans (oneCommon p q ne))

theorem rectangleWeight (r : Rectangle) (good : valid r) :
    6 * (r.1.card * r.2.card) ≤ 5 * (r.1.card + r.2.card) := by
  by_cases a0 : r.1.card = 0
  · simp [a0]
  by_cases b0 : r.2.card = 0
  · simp [b0]
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < r.1.card)
  obtain ⟨l, hl⟩ := Finset.card_pos.mp (by omega : 0 < r.2.card)
  have inLines (x) (hx : x ∈ r.1) : r.2 ⊆ linesThrough x := by
    exact fun y hy => Finset.mem_filter.mpr ⟨Finset.mem_univ _, good x hx y hy⟩
  have inPoints : r.1 ⊆ pointsOn l := by
    exact fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, good x hx l hl⟩
  have da := Finset.card_le_card inPoints
  have db := Finset.card_le_card (inLines p hp)
  rw [degreeL] at da
  rw [degreeP] at db
  by_cases a1 : r.1.card ≤ 1
  · have ha : r.1.card = 1 := by omega
    rw [ha, Nat.one_mul]
    omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (by omega : 1 < r.1.card)
  have sub : r.2 ⊆ linesThrough u ∩ linesThrough v :=
    fun y hy => Finset.mem_inter.mpr ⟨inLines u hu hy, inLines v hv hy⟩
  have hb := (Finset.card_le_card sub).trans (oneCommon u v huv)
  have h1 : r.2.card = 1 := by omega
  rw [h1, Nat.mul_one]
  omega

private theorem listWeight (rs : List Rectangle) (h : ∀ r ∈ rs, valid r) :
    6 * (covered rs).card ≤ 5 * weight rs := by
  induction rs with
  | nil => simp [covered, weight]
  | cons r rs ih =>
    have headBound := rectangleWeight r (h r List.mem_cons_self)
    have tailBound := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have unionBound := Finset.card_union_le (r.1.product r.2) (covered rs)
    have cardEq : (r.1.product r.2).card = r.1.card * r.2.card :=
      Finset.card_product _ _
    rw [cardEq] at unionBound
    simp only [covered, weight]
    omega

theorem gateLowerBound (rs : List Rectangle) (h : ∀ r ∈ rs, valid r)
    (allFlags : flags ⊆ covered rs) : 125 ≤ weight rs - 1 := by
  have n := Finset.card_le_card allFlags
  rw [numberOfFlags] at n
  have bound := listWeight rs h
  omega

def rectangleGates (r : Rectangle) : ℕ := (r.1.card - 1) + (r.2.card - 1) + 1

def formulaGates (rs : List Rectangle) : ℕ :=
  (rs.map rectangleGates).sum + (rs.length - 1)

private theorem addCombineGates (rs : List Rectangle)
    (sides : ∀ r ∈ rs, 0 < r.1.card ∧ 0 < r.2.card) :
    (rs.map rectangleGates).sum + rs.length = weight rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have h := sides r List.mem_cons_self
    have t := ih (fun x hx => sides x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.sum_cons, List.length_cons, rectangleGates, weight]
    omega

theorem rectangleFormulaLowerBound (rs : List Rectangle) (h : ∀ r ∈ rs, valid r)
    (sides : ∀ r ∈ rs, 0 < r.1.card ∧ 0 < r.2.card) (allFlags : flags ⊆ covered rs) :
    125 ≤ formulaGates rs := by
  have lower := gateLowerBound rs h allFlags
  have count := addCombineGates rs sides
  unfold formulaGates
  omega

def lineStars : List Rectangle :=
  (List.finRange 21).map fun l => (pointsOn l, {l})

theorem lineStarsValid : ∀ r ∈ lineStars, valid r := by
  intro r hr p hp l hl
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hr
  have hkl : l = k := Finset.mem_singleton.mp hl
  subst l
  exact (Finset.mem_filter.mp hp).2

private theorem memCovered (e : Index × Index) (rs : List Rectangle) :
    e ∈ covered rs ↔ ∃ r ∈ rs, e.1 ∈ r.1 ∧ e.2 ∈ r.2 := by
  induction rs with
  | nil => simp [covered]
  | cons r rs ih =>
    simp [covered, Finset.mem_product, ih]

theorem lineStarsCover : covered lineStars = flags := by
  ext e
  simp [memCovered, lineStars, flags, pointsOn]

theorem lineStarsNonempty : ∀ r ∈ lineStars, 0 < r.1.card ∧ 0 < r.2.card := by
  intro r hr
  obtain ⟨l, _, rfl⟩ := List.mem_map.mp hr
  simp [degreeL]

theorem lineStarsCost : formulaGates lineStars = 125 := by decide

end Plane4RectangleCover
