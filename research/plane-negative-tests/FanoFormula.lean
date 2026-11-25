import KWWeight
import Mathlib.Data.Finset.Powerset

namespace FanoFormula
open KWPartition KWWeight
abbrev V := Fin 14
abbrev R := Fin 21
abbrev C := Fin 37
def edges : Array Nat := #[129,257,1025,258,514,2050,516,1028,4100,1032,2056,8200,144,2064,4112,288,4128,8224,192,576,8256]
def cols : Array Nat := #[16256,14849,13442,12291,10628,10245,8326,5000,4617,4234,396,10000,8721,9234,8468,8215,792,3744,2593,1186,2212,680,174,1584,569,7488,6209,5186,2372,4424,4171,1360,348,3168,2149,1138,127]
def minus : Array Nat := #[38688262144,34364063748,4299161744,17196777474,21508390928,4311746688,35467034628,1090519170,34376648704,17179901970,34359773188,51573293056,18287165442,1077936260,17184194576,1073774598,4295002128,5402263680,16812034,4227092,21102720]
def one : Array Nat := #[18270552212,18303977616,18304108548,35471263888,35437840514,35471392786,21479196802,21512751108,21512618118,5423368196,5423366162,5389682710,38671646868,38705201170,38705070214,51594135696,51594133638,51560581142,56908447892,56908449922,56908318742]
def two : Array Nat := #[4194306,4294967298,34359738370,4294967300,16777220,17179869188,16777232,34359738384,1073741840,34359738496,17179869312,32896,4196352,17179871232,1073743872,4295098368,1073872896,163840,37748736,50331648,33587200]
def w (i : R) (j : C) : Int :=
  if (one[i.val]?.getD 0).testBit j.val then 1 else if (two[i.val]?.getD 0).testBit j.val then 2 else
  if (minus[i.val]?.getD 0).testBit j.val then -1 else 0
def yes (i : R) (v : V) := (edges[i.val]?.getD 0).testBit v.val
def no (j : C) (v : V) := (cols[j.val]?.getD 0).testBit v.val
def source (x : V → Bool) : Bool := ((((((((x 0) && (((x 7) || (x 8)) || (x 10))) || ((x 1) && (((x 8) || (x 9)) || (x 11)))) || ((x 2) && (((x 9) || (x 10)) || (x 12)))) || ((x 3) && (((x 10) || (x 11)) || (x 13)))) || ((x 4) && (((x 7) || (x 11)) || (x 12)))) || ((x 5) && (((x 8) || (x 12)) || (x 13)))) || ((x 6) && (((x 7) || (x 9)) || (x 13))))
def upper : Formula V := (.join (.join (.join (.join (.join (.join (.meet (.var 0) (.join (.join (.var 7) (.var 8)) (.var 10))) (.meet (.var 1) (.join (.join (.var 8) (.var 9)) (.var 11)))) (.meet (.var 2) (.join (.join (.var 9) (.var 10)) (.var 12)))) (.meet (.var 3) (.join (.join (.var 10) (.var 11)) (.var 13)))) (.meet (.var 4) (.join (.join (.var 7) (.var 11)) (.var 12)))) (.meet (.var 5) (.join (.join (.var 8) (.var 12)) (.var 13)))) (.meet (.var 6) (.join (.join (.var 7) (.var 9)) (.var 13))))

theorem upper_eval (x : V → Bool) : upper.eval x = source x := rfl
theorem gates : upper.gates = 27 := by decide +kernel
theorem row_yes : ∀ r, source (yes r) = true := by decide +kernel
theorem col_no : ∀ j, source (no j) = false := by decide +kernel
def star (v : V) : Finset R := Finset.univ.filter fun i => yes i v = true
def allowed (v : V) : Finset C := Finset.univ.filter fun j => no j v = false
set_option maxHeartbeats 0 in
theorem full_mass : mass w Finset.univ Finset.univ = 168 := by decide +kernel
set_option maxHeartbeats 0 in
theorem limits : ∀ v : V, ∀ A ∈ (star v).powerset, ∑ j ∈ allowed v, max 0 (∑ i ∈ A, w i j) ≤ 6 := by decide +kernel

theorem rectangles (v : V) (A : Finset R) (B : Finset C) (pos : ∀ i ∈ A, yes i v = true)
    (neg : ∀ j ∈ B, no j v = false) : mass w A B ≤ 6 := by
  have hs : A ⊆ star v := fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _,pos i hi⟩
  have hn : B ⊆ allowed v := fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _,neg j hj⟩
  exact (cap w A B (allowed v) hn).trans (limits v A (Finset.mem_powerset.mpr hs))

theorem exact_size (k : Nat) : (∃ f : Formula V, f.gates ≤ k ∧ ∀ x, f.eval x = source x) ↔ 27 ≤ k := by
  constructor
  · rintro ⟨f,small,h⟩
    have lo := lower yes no w 6 rectangles f Finset.univ Finset.univ
      (fun i _ => (h (yes i)).trans (row_yes i)) (fun j _ => (h (no j)).trans (col_no j))
    rw [full_mass,Formula.leaf_count] at lo
    omega
  · intro h
    exact ⟨upper,gates.le.trans h,upper_eval⟩
end FanoFormula
