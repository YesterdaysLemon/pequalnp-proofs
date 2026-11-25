import FamilyLive
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Prod

/-! Normalized Boolean wires, paired restrictions, and two-coordinate separation. -/
namespace Paired
abbrev SmallCoord := Bool × Bool
abbrev SmallRow := SmallCoord → Bool
def onTwo (x : SmallRow) : Bool :=
  (x (false,false) || x (true,false)) &&
    (x (false,false) || !x (false,true)) && (x (true,false) || !x (true,true))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxSize 1024 in
set_option synthInstance.maxHeartbeats 100000 in
theorem two_separates : ∀ (p q : SmallCoord), p ≠ q → ∀ o : Bool → Bool → Bool,
    ∃ x y : SmallRow, onTwo x ≠ onTwo y ∧ o (x p) (x q) = o (y p) (y q) ∧
      ∀ d : SmallCoord, d ≠ p → d ≠ q → x d = y d := by decide +kernel

noncomputable section
open Classical LiveRestriction

abbrev Coord := ℕ × Bool
abbrev Row := Coord → Bool
abbrev Wire := Row → Bool
abbrev Op := Bool → Bool → Bool

def zero : Wire := fun _ => false
def input (p : Coord) : Wire := fun x => x p
def bank (s : Finset ℕ) : Finset Wire :=
  (s ×ˢ (Finset.univ : Finset Bool)).image input

-- The first coordinate of each pair stores the complement of the physical a input.
-- The output is complemented as well. The all-false row is the neutral row.
def condition (s : Finset ℕ) (x : Row) : Prop :=
  (∃ i ∈ s, x (i,false) = true) ∧ (∀ i ∈ s, x (i,false) = true ∨ x (i,true) = false)
def target (s : Finset ℕ) : Wire := fun x => decide (condition s x)

def combine (o : Op) (a b : Wire) : Wire := fun x => o (a x) (b x)
def ops (a b : Wire) : Finset Wire :=
  ((Finset.univ : Finset Op).filter fun o => o false false = false).image
    (fun o => combine o a b)

theorem ops_spec {a b z : Wire} :
    z ∈ ops a b ↔ ∃ o : Op, o false false = false ∧ combine o a b = z := by
  simp [ops]

theorem input_injective : Function.Injective input := by
  intro p q h
  by_contra hn
  have eq := congrFun h (fun i => decide (i = p))
  simp [input] at eq
  exact hn eq.symm

theorem bank_spec {s : Finset ℕ} {w : Wire} :
    w ∈ bank s ↔ ∃ p : Coord, p.1 ∈ s ∧ input p = w := by
  simp [bank, Finset.mem_image]

theorem primary_mem {s : Finset ℕ} {p : Coord} (h : p.1 ∈ s) : input p ∈ bank s :=
  bank_spec.mpr ⟨p, h, rfl⟩

theorem bank_card (s : Finset ℕ) : (bank s).card = s.card * 2 := by
  rw [bank, Finset.card_image_of_injective _ input_injective, Finset.card_product]
  rfl

def pin (i : ℕ) (x : Row) : Row := fun p => if p.1 = i then false else x p
def restrict (i : ℕ) (w : Wire) : Wire := fun x => w (pin i x)

theorem restrict_input (i : ℕ) (p : Coord) :
    restrict i (input p) = if p.1 = i then zero else input p := by
  by_cases h : p.1 = i <;> ext x <;> simp [restrict, pin, input, zero, h]

theorem restrict_target (s : Finset ℕ) (i : ℕ) :
    restrict i (target s) = target (s.erase i) := by
  funext x
  change decide (condition s (pin i x)) = decide (condition (s.erase i) x)
  congr 1
  apply propext
  unfold condition
  simp only [pin, Finset.mem_erase]
  constructor
  · rintro ⟨⟨j, hj, hit⟩, all⟩
    have ne : j ≠ i := by rintro rfl; simp at hit
    refine ⟨⟨j, ⟨ne,hj⟩, by simpa [ne] using hit⟩, ?_⟩
    rintro j ⟨hne,hj⟩
    simpa [hne] using all j hj
  · rintro ⟨⟨j, ⟨ne,hj⟩, hit⟩, all⟩
    refine ⟨⟨j, hj, by simpa [ne] using hit⟩, ?_⟩
    intro j hj
    by_cases h : j = i
    · simp [h]
    · simpa [h] using all j ⟨h,hj⟩

theorem project_bank (s : Finset ℕ) (i : ℕ) :
    project (restrict i) zero (bank s) ⊆ bank (s.erase i) := by
  intro w hw
  obtain ⟨nz, h⟩ := Finset.mem_erase.mp hw
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp h
  obtain ⟨p,hp,rfl⟩ := bank_spec.mp hu
  rw [restrict_input] at nz ⊢
  split_ifs with eq
  · exact (nz (by simp [eq])).elim
  · exact primary_mem (Finset.mem_erase.mpr ⟨eq,hp⟩)

theorem op_preserved (i : ℕ) (a b z : Wire) (hz : z ∈ ops a b) :
    restrict i z ∈ ops (restrict i a) (restrict i b) := by
  obtain ⟨o, ho, rfl⟩ := ops_spec.mp hz
  exact ops_spec.mpr ⟨o,ho,rfl⟩

theorem unary_wire (f : Bool → Bool) (hf : f false = false) (w : Wire) :
    (fun x => f (w x)) = zero ∨ (fun x => f (w x)) = w := by
  cases h : f true
  · left; funext x; cases hx : w x <;> simp [zero,h,hf]
  · right; funext x; cases hx : w x <;> simp [h,hf]

theorem op_simple {a b z : Wire} (hz : z ∈ ops a b) (h : a = zero ∨ b = zero ∨ a = b) :
    z = zero ∨ z = a ∨ z = b := by
  obtain ⟨o,ho,rfl⟩ := ops_spec.mp hz
  rcases h with rfl | rfl | rfl
  · rcases unary_wire (o false) ho b with e | e
    · exact .inl e
    · exact .inr (.inr e)
  · rcases unary_wire (fun t => o t false) ho a with e | e
    · exact .inl e
    · exact .inr (.inl e)
  · rcases unary_wire (fun t => o t t) ho a with e | e
    · exact .inl e
    · exact .inr (.inl e)

theorem live_distinguishes {g : Wire} {k : ℕ} {s : Finset Wire}
    (h : live ops g k s) (x y : Row) (neq : g x ≠ g y) : ∃ w ∈ s, w x ≠ w y := by
  apply live_separates (fun w : Wire => w x ≠ w y) neq _ h
  intro a b z hz diff
  obtain ⟨o,_,rfl⟩ := ops_spec.mp hz
  by_contra! same
  exact diff (by simp [combine,same.1,same.2])

def tag (i j : ℕ) (p : SmallCoord) : Coord := (if p.1 then j else i, p.2)
def embed (i j : ℕ) (x : SmallRow) : Row := fun p =>
  if p.1 = i then x (false,p.2) else if p.1 = j then x (true,p.2) else false

theorem embed_tag {i j : ℕ} (ne : i ≠ j) (x : SmallRow) (p : SmallCoord) :
    embed i j x (tag i j p) = x p := by
  rcases p with ⟨b,t⟩
  cases b <;> simp [embed,tag,ne.symm]

theorem target_embed {s : Finset ℕ} {i j : ℕ} (hi : i ∈ s) (hj : j ∈ s) (ne : i ≠ j)
    (x : SmallRow) : target s (embed i j x) = onTwo x := by
  apply Bool.eq_iff_iff.mpr
  simp only [onTwo,Bool.and_eq_true,Bool.or_eq_true,
    Bool.not_eq_true']
  constructor
  · intro proof
    obtain ⟨⟨k,hk,hv⟩,all⟩ := (of_decide_eq_true proof : condition s (embed i j x))
    refine ⟨⟨?_,by simpa [embed] using all i hi⟩,by simpa [embed,ne.symm] using all j hj⟩
    by_cases e : k = i
    · exact .inl (by simpa [embed,e] using hv)
    · have e' : k = j := by by_contra h; simp [embed,e,h] at hv
      exact .inr (by simpa [embed,e,e',ne.symm] using hv)
  · rintro ⟨⟨first,ai⟩,aj⟩
    apply decide_eq_true
    constructor
    · rcases first with h | h
      · exact ⟨i,hi,by simpa [embed] using h⟩
      · exact ⟨j,hj,by simpa [embed,ne.symm] using h⟩
    · intro k _
      by_cases e : k = i
      · simpa [embed,e] using ai
      by_cases d : k = j
      · simpa [embed,e,d,ne.symm] using aj
      · simp [embed,e,d]

theorem find_pair {s : Finset ℕ} (hs : 2 ≤ s.card) (p q : Coord)
    (hp : p.1 ∈ s) (hq : q.1 ∈ s) :
    ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ ∃ u v : SmallCoord, tag i j u = p ∧ tag i j v = q := by
  rcases p with ⟨i,t⟩
  rcases q with ⟨j,u⟩
  by_cases eq : i = j
  · subst j
    obtain ⟨j,hj,ne⟩ := Finset.exists_mem_ne (a := i) (by omega : 1 < s.card)
    exact ⟨i,hp,j,hj,ne.symm,(false,t),(false,u),rfl,rfl⟩
  · exact ⟨i,hp,j,hq,eq,(false,t),(true,u),rfl,rfl⟩

theorem pair_separates {s : Finset ℕ} (hs : 2 ≤ s.card) (p q : Coord)
    (hp : p.1 ∈ s) (hq : q.1 ∈ s) (ne : p ≠ q) (o : Op) :
    ∃ x y : Row, target s x ≠ target s y ∧ o (x p) (x q) = o (y p) (y q) ∧
      ∀ d : Coord, d ≠ p → d ≠ q → x d = y d := by
  obtain ⟨i,hi,j,hj,nij,u,v,rfl,rfl⟩ := find_pair hs p q hp hq
  have uv : u ≠ v := fun h => ne (congrArg (tag i j) h)
  obtain ⟨x,y,diff,eq,out⟩ := two_separates u v uv o
  refine ⟨embed i j x,embed i j y,?_,?_,?_⟩
  · simpa only [target_embed hi hj nij] using diff
  · simpa only [embed_tag nij] using eq
  · rintro ⟨k,t⟩ h₁ h₂
    by_cases ei : k = i
    · subst k
      exact (embed_tag nij x (false,t)) ▸ (embed_tag nij y (false,t)) ▸
        out (false,t) (fun h => h₁ (congrArg (tag i j) h)) (fun h => h₂ (congrArg (tag i j) h))
    by_cases ej : k = j
    · subst k
      simpa [embed,nij.symm] using out (true,t)
        (fun h => h₁ (congrArg (tag i j) h)) (fun h => h₂ (congrArg (tag i j) h))
    · simp [embed,ei,ej]

end
end Paired
