import G11Upper
import KWSemantics
import Mathlib.Data.Finset.Powerset

namespace G11Game
open KWPartition
abbrev V := Fin 11
abbrev R := Fin 16
abbrev C := Fin 24
abbrev T := Rect R C V
abbrev Key := V × Finset R
def tag (t : T) : Key := (t.label,t.rows)
def wordKey (p : Nat) : Key :=
  (Fin.ofNat 11 (label p),Finset.univ.filter fun i : R => (members p).testBit i.val = true)
def library := (List.range 85).map wordKey
def incident (v : V) := Finset.univ.filter fun i : R => yes i v = true

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem exhaustive : ∀ v : V, ∀ a ∈ (incident v).powerset.erase ∅, (v,a) ∈ library := by decide +kernel

theorem label_sound : ∀ p : Fin 85, ∀ j : C, game.col p.val j.val = !(no j (wordKey p).1) := by decide +kernel
theorem row_sound (p : Nat) (i : R) : game.row p i.val = true ↔ i ∈ (wordKey p).2 := by
  simp [game,wordKey]

def index (t : T) := library.idxOf (tag t)

theorem indexed {t : T} (v : valid yes no t) (row : t.rows.Nonempty) :
    index t < 85 ∧ wordKey (index t) = tag t := by
  have sub : t.rows ⊆ incident t.label := fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _,v.1 i hi⟩
  have inside := exhaustive t.label t.rows (Finset.mem_erase.mpr ⟨row.ne_empty,Finset.mem_powerset.mpr sub⟩)
  change tag t ∈ library at inside
  have lt := List.idxOf_lt_length_of_mem inside
  have eq := @List.getElem_idxOf _ _ _ (tag t) library lt
  constructor
  · simpa [index,library] using lt
  · change library[index t]'lt = tag t at eq
    change wordKey (index t) = tag t
    simp only [library,List.getElem_map,List.getElem_range] at eq
    exact eq

def live (L : List T) (p j : Nat) : Bool :=
  L.any fun t => decide (index t = p ∧ j < 24 ∧
    j ∈ t.cols.image Fin.val ∧ t.rows.Nonempty)

theorem live_iff (L : List T) (p : Nat) (j : C) : live L p j.val = true ↔
    ∃ t ∈ L, index t = p ∧ j ∈ t.cols ∧ t.rows.Nonempty := by
  have equiv (t : T) : j.val ∈ t.cols.image Fin.val ↔ j ∈ t.cols := by
    constructor
    · intro hm
      obtain ⟨k,hi,e⟩ := Finset.mem_image.mp hm
      exact Fin.ext e ▸ hi
    · exact Finset.mem_image_of_mem _
  simp only [live,List.any_eq_true,decide_eq_true_eq,j.isLt,true_and,equiv]

def picked (L : List T) (p : Nat) : Bool := decide (p ∈ L.map index)

theorem count_picked (L : List T) :
    (List.range 85).countP (picked L) ≤ L.length := by
  have nd : (List.range 85).Nodup := List.nodup_range
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (nd.filter (picked L))]
  have sub : ((List.range 85).filter (picked L)).toFinset ⊆ (L.map index).toFinset := by
    intro p hp
    simpa [picked] using (List.mem_filter.mp (List.mem_toFinset.mp hp)).2
  exact (Finset.card_le_card sub).trans (by simpa using (List.toFinset_card_le (l := L.map index)))

noncomputable def selection (f : Formula V) (ev : ∀ x, f.eval x = graph x) (small : f.gates ≤ 21) :
    KWEncoding.Selection game 22 := by
  let L := tiles yes no f Finset.univ Finset.univ
  have good : ∀ t ∈ L, valid yes no t := all_valid yes no f _ _
    (fun i _ => (ev _).trans (rows_positive i)) (fun j _ => (ev _).trans (cols_negative j))
  have single (i : R) (j : C) : ∃ t, L.filter (hits i j) = [t] := by
    apply List.length_eq_one_iff.mp
    rw [← List.countP_eq_length_filter]
    simpa [L] using partition yes no f Finset.univ Finset.univ i j
  refine ⟨picked L,live L,?_,?_,?_,?_⟩
  · intro p hp j hj _ a
    obtain ⟨t,ht,eq,_,_⟩ := (live_iff L p ⟨j,hj⟩).mp a
    exact decide_eq_true (List.mem_map.mpr ⟨t,ht,eq⟩)
  · intro ri hr cj hj
    let i : R := ⟨ri,hr⟩
    let j : C := ⟨cj,hj⟩
    obtain ⟨t,eq⟩ := single i j
    have mem : t ∈ L.filter (hits i j) := by rw [eq]; simp
    obtain ⟨ht,m⟩ := List.mem_filter.mp mem
    obtain ⟨row,col⟩ := of_decide_eq_true m
    have nonempty := (show t.rows.Nonempty from ⟨i,row⟩)
    obtain ⟨lt,tagEq⟩ := indexed (good t ht) nonempty
    have ri_in : game.row (index t) ri = true := (row_sound _ i).mpr (by simpa [tagEq,tag] using row)
    have cj_in : game.col (index t) cj = true := by
      rw [label_sound ⟨index t,lt⟩ j,tagEq]
      simp [tag,(good t ht).2 j col]
    refine ⟨index t,List.mem_filter.mpr ⟨List.mem_range.mpr lt,by simp [ri_in,cj_in]⟩,?_⟩
    exact (live_iff L _ j).mpr ⟨t,ht,rfl,col,nonempty⟩
  · intro ri hr cj hj p hp q hq a d
    let i : R := ⟨ri,hr⟩
    let j : C := ⟨cj,hj⟩
    obtain ⟨only,one⟩ := single i j
    have unique (k : Nat) (hk : k ∈ KWEncoding.options game ri cj) (act : live L k cj = true) :
        index only = k := by
      obtain ⟨t,ht,e,col,ne⟩ := (live_iff L _ j).mp act
      have inRow := (row_sound k i).mp (Bool.and_eq_true_iff.mp (List.mem_filter.mp hk).2).1
      have tags := (indexed (good t ht) ne).2
      rw [← e,tags] at inRow
      have mem : t ∈ L.filter (hits i j) := List.mem_filter.mpr ⟨ht,decide_eq_true ⟨inRow,col⟩⟩
      rw [one] at mem
      simpa [List.mem_singleton.mp mem] using e
    exact (unique p hp a).symm.trans (unique q hq d)
  · have h := count_picked L
    change (List.range 85).countP (picked L) ≤ 22
    have len := size_tiles yes no f (Finset.univ : Finset R) (Finset.univ : Finset C)
    change L.length = f.leaves at len
    rw [Formula.leaf_count] at len
    omega

theorem exact_size (certificate : (KWEncoding.problem game 22).Unsat) (k : Nat) :
    (∃ f : Formula V, f.gates ≤ k ∧ ∀ x, f.eval x = graph x) ↔ 22 ≤ k := by
  constructor
  · rintro ⟨f,bd,ev⟩
    by_contra low
    exact KWEncoding.impossible certificate (selection f ev (by omega))
  · intro bd
    exact ⟨star,star_size ▸ bd,star_correct⟩

end G11Game
