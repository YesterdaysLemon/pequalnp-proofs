import MajoritySlices

namespace FiveMajority
open Paired Paired.Split FullSearch LiveRestriction FirstGate
noncomputable section
open Classical

def prim := primaryBank keys.toFinset

theorem primary {w : Wire} : w ∈ prim ↔ ∃ i : Fin 5, input (coord i) = w := by
  constructor
  · intro h
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hp)
    exact ⟨i,rfl⟩
  · rintro ⟨i,rfl⟩
    exact Finset.mem_image_of_mem _ (List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨i,rfl⟩))

theorem norm_on (r : Nat) : normalize fn (expand r) = vote (onRow r) := by
  have anchor : fn baseline = false := by decide
  change (fn (expand r) ^^ fn baseline) = _
  rw [anchor,Bool.xor_false]
  rfl

theorem not_primary : normalize fn ∉ prim := by
  intro h
  obtain ⟨i,eq⟩ := primary.mp h
  let r := 2^i.val
  have tbl : ∀ i : Fin 5, vote (onRow (2^i.val)) ≠ onRow (2^i.val) i := by decide +kernel
  apply tbl i
  have e := congrFun eq (expand r)
  rw [norm_on] at e
  exact e.symm

theorem retained {i j : Fin 5} {o : Op} {one : Bool} (hit : collision i j o one)
    {rest : Finset Wire} (sub : rest ⊆ prim) {k : Nat}
    (h : live Paired.ops (normalize fn) k (insert (combine o (input (coord i)) (input (coord j))) rest)) :
    ∃ v : Fin 5, input (coord v) ∈ rest ∧ (v = i ∨ (v = j ∧ one = false)) := by
  let code := witness i j o one
  let x := expand (code/32)
  let y := expand (code%32)
  rcases hit with ⟨diff,same,other⟩
  have d : normalize fn x ≠ normalize fn y := by simpa only [x,y,norm_on,code] using diff
  obtain ⟨w,mem,neq⟩ := live_distinguishes h x y d
  rcases Finset.mem_insert.mp mem with rfl | mem
  · exact (neq same).elim
  obtain ⟨v,rfl⟩ := primary.mp (sub mem)
  refine ⟨v,mem,?_⟩
  by_cases a : v = i
  · exact Or.inl a
  by_cases b : v = j
  · cases one with
    | false => exact Or.inr ⟨b,rfl⟩
    | true => exact (neq (other v a (.inl rfl))).elim
  · exact (neq (other v a (.inr b))).elim

theorem projected_tail {i j p : Fin 5} {o : Op} {b : Bool} {rest : Finset Wire}
    (side : p = i ∨ p = j) (zeroBase : o false false = false) (hr : rest ⊆ prim) {k : Nat}
    (run : live Paired.ops (normalize fn) k (insert (combine o (input (coord i)) (input (coord j))) rest)) :
    7 + zeroCount (pack (samples p b)) 0 (insert (combine o (input (coord i)) (input (coord j))) rest) ≤ k := by
  let P := pack (samples p b)
  have small (w : Wire) (hw : w ∈ prim) : P w = 0 ∨ P w ∈ ThresholdFour.inputs := by
    obtain ⟨v,rfl⟩ := primary.mp hw
    exact small_words p v b
  have hop : combine o (input (coord i)) (input (coord j)) ∈ Paired.ops (input (coord i)) (input (coord j)) :=
    ops_spec.mpr ⟨o,zeroBase,rfl⟩
  have collapse : P (input (coord i)) = 0 ∨ P (input (coord j)) = 0 ∨ P (input (coord i)) = P (input (coord j)) := by
    rcases side with rfl | rfl
    · exact .inl (lost_pin _ _)
    · exact .inr (.inl (lost_pin _ _))
  have first := extended_simple (pack_preserves (samples p b) _ _ _ hop) collapse
  apply ThresholdFour.live_lower _ (goal_word p b) _ run
  intro w hw
  obtain ⟨nz,packed⟩ := Finset.mem_erase.mp hw
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp packed
  apply List.mem_toFinset.mpr
  change P u ≠ 0 at nz
  change P u ∈ ThresholdFour.inputs
  rcases Finset.mem_insert.mp hu with rfl | old
  · rcases first with e | e | e
    · exact (nz e).elim
    · change P _ = P _ at e
      rw [e] at nz ⊢
      exact (small_words p i b).resolve_left nz
    · change P _ = P _ at e
      rw [e] at nz ⊢
      exact (small_words p j b).resolve_left nz
  · exact (small u (hr old)).resolve_left nz

theorem root_lower (all : Bool) {k : Nat}
    (run : build (family all) (normalize fn) k prim) : (if all then 9 else 10) ≤ k := by
  obtain ⟨s,sub,lv⟩ := compress run
  have notDone : s ≠ {normalize fn} := fun e => not_primary (sub (e ▸ Finset.mem_singleton_self _))
  cases k with
  | zero => exact (notDone lv).elim
  | succ k =>
    obtain done | ⟨a,ha,b,hb,ne,z,hz,hn,r,he,tail⟩ := first_live lv
    · exact (notDone done).elim
    obtain ⟨i,rfl⟩ := primary.mp (sub ha)
    obtain ⟨j,rfl⟩ := primary.mp (sub hb)
    have ij : i ≠ j := fun e => ne (congrArg (fun v => input (coord v)) e)
    obtain ⟨o,⟨atZero,allowed⟩,rfl⟩ := member.mp hz
    have hr : r ⊆ prim := by
      apply Finset.Subset.trans _ sub
      rw [he]
      exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
    have wide := relax tail
    cases all with
    | true =>
      obtain ⟨v,hv,side⟩ := retained (pair_collision i j ij o) hr wide
      have pos : 0 < zeroCount (pack (samples v false)) 0
          (insert (combine o (input (coord i)) (input (coord j))) r) :=
        Finset.card_pos.mpr ⟨input (coord v),Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hv,lost_pin ..⟩⟩
      have lower := projected_tail (b := false) (side.imp_right And.left) atZero hr wide
      simp; omega
    | false =>
      have left : ¬(∀ u v, o u v = u) := by
        intro proj
        have eq : combine o (input (coord i)) (input (coord j)) = input (coord i) := funext fun x => proj _ _
        apply hn
        rw [eq]
        exact ha
      have right : ¬(∀ u v, o u v = v) := by
        intro proj
        have eq : combine o (input (coord i)) (input (coord j)) = input (coord j) := funext fun x => proj _ _
        apply hn
        rw [eq]
        exact hb
      have u2 : parity o = false := allowed.resolve_left (by decide)
      obtain ⟨v,hv,d⟩ := retained (one_collision i j ij o atZero u2 left right) hr wide
      obtain rfl | bad := d
      · obtain ⟨b,canalized⟩ := canal o atZero u2 right
        have two : 2 ≤ zeroCount (pack (samples v b)) 0 (insert (combine o (input (coord v)) (input (coord j))) r) :=
          Finset.one_lt_card.mpr ⟨input (coord v),Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hv,lost_pin ..⟩,
            _,Finset.mem_filter.mpr ⟨Finset.mem_insert_self ..,lost_gate canalized⟩,fun e => hn (e ▸ ha)⟩
        have lower := projected_tail (p := v) (b := b) (.inl rfl) atZero hr wide
        simp; omega
      · cases bad.2

end
end FiveMajority
