import FullSearch

namespace FullSearch
open LiveRestriction

abbrev Samples := Fin 512 → Paired.Row

def word (f : Fin 512 → Bool) : W := (BitVec.ofBoolListLE (List.ofFn f)).setWidth 512
theorem word_at (f : Fin 512 → Bool) (i : Fin 512) : (word f)[i.val] = f i := by
  change (word f).getLsbD i.val = _
  rw [word, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBoolListLE]
  have hi : i.val < (List.ofFn f).length := by simpa only [List.length_ofFn] using i.isLt
  simp only [i.isLt,decide_true,Bool.true_and,List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi,Option.getD_some,List.getElem_ofFn]

def pack (r : Samples) (w : Paired.Wire) : W := word fun j => w (r j) ^^ w (r 0)

theorem pack_at (r : Samples) (w : Paired.Wire) (i : Fin 512) :
    (pack r w)[i.val] = (w (r i) ^^ w (r 0)) := word_at ..

def extended (a b : W) : Finset W := insert 0 (insert a (insert b (basicOps a b)))

def coded (f : Paired.Op) (a b : W) : W :=
  if f false true then
    if f true false then (if f true true then a ||| b else a ^^^ b)
    else if f true true then b else b &&& ~~~a
  else if f true false then (if f true true then a else a &&& ~~~b)
    else if f true true then a &&& b else 0

theorem coded_mem (f : Paired.Op) (a b : W) : coded f a b ∈ extended a b := by
  cases ft : f false true <;> cases tf : f true false <;> cases tt : f true true <;>
    simp [coded,extended,basicOps,ops,ft,tf,tt]

theorem coded_at (f : Paired.Op) (base : f false false = false) (a b : W) (i : Fin 512) :
    (coded f a b)[i.val] = f a[i.val] b[i.val] := by
  cases ft : f false true <;> cases tf : f true false <;> cases tt : f true true <;>
    cases av : a[i.val] <;> cases bv : b[i.val] <;> simp [coded,ft,tf,tt,av,bv,base]

theorem pack_preserves (r : Samples) (a b z : Paired.Wire) (hz : z ∈ Paired.ops a b) :
    pack r z ∈ extended (pack r a) (pack r b) := by
  obtain ⟨o,_,rfl⟩ := Paired.ops_spec.mp hz
  let f : Paired.Op := fun u v => o (u ^^ a (r 0)) (v ^^ b (r 0)) ^^ o (a (r 0)) (b (r 0))
  have base : f false false = false := by simp [f]
  convert coded_mem f (pack r a) (pack r b) using 1
  apply BitVec.eq_of_getElem_eq
  intro i hi
  let j : Fin 512 := ⟨i,hi⟩
  change (pack r (Paired.combine o a b))[j.val] = (coded f (pack r a) (pack r b))[j.val]
  rw [coded_at f base _ _ j,pack_at,pack_at,pack_at]
  simp [Paired.combine,f]

set_option maxRecDepth 10000 in
set_option exponentiation.threshold 1024 in
theorem extended_simple {a b z : W} (hz : z ∈ extended a b) (h : a = 0 ∨ b = 0 ∨ a = b) :
    z = 0 ∨ z = a ∨ z = b := by
  simp only [extended,Finset.mem_insert,basicOps,ops,List.mem_toFinset,List.mem_cons,
    List.not_mem_nil,or_false] at hz
  rcases h with rfl | rfl | rfl <;>
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · exact Or.inr (BitVec.and_allOnes (x := b))
  · exact Or.inr (Or.inl (BitVec.and_allOnes (x := a)))

theorem clean_live {g : W} (ng : g ≠ 0) {k : ℕ} {s : Finset W}
    (h : live extended g k s) : 0 ∉ s ∧ live basicOps g k s := by
  induction k generalizing s with
  | zero =>
    change s = {g} at h
    exact ⟨fun hs => ng (Finset.mem_singleton.mp (h ▸ hs)).symm,h⟩
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,ne,z,hz,hn,r,he,tail⟩
    · obtain ⟨ns,ok⟩ := ih skip
      exact ⟨ns,Or.inl ok⟩
    obtain ⟨zt,ok⟩ := ih tail
    have nz : z ≠ 0 := fun eq => zt (eq ▸ Finset.mem_insert_self ..)
    have nzr : 0 ∉ r := fun e => zt (Finset.mem_insert_of_mem e)
    have simple : ¬(a = 0 ∨ b = 0 ∨ a = b) := by
      intro e
      rcases extended_simple hz e with n | l | r'
      · exact nz n
      · exact hn (l ▸ ha)
      · exact hn (r' ▸ hb)
    have a0 : 0 ≠ a := fun e => simple (.inl e.symm)
    have b0 : 0 ≠ b := fun e => simple (.inr (.inl e.symm))
    have hit : z ∈ basicOps a b := by
      simp only [extended,Finset.mem_insert] at hz
      rcases hz with e | e | e | mem
      · exact (nz e).elim
      · exact (hn (e ▸ ha)).elim
      · exact (hn (e ▸ hb)).elim
      · exact mem
    refine ⟨?_,Or.inr ⟨a,ha,b,hb,ne,z,hit,hn,r,he,ok⟩⟩
    rw [he]
    intro h0
    rcases Finset.mem_insert.mp h0 with eq | h0
    · exact a0 eq
    · exact (Finset.mem_insert.mp h0).elim b0 nzr

theorem live_build {α : Type*} [DecidableEq α] {op : α → α → Finset α}
    {g : α} {k : ℕ} {s : Finset α} (h : live op g k s) : build op g k s := by
  induction k generalizing s with
  | zero => change s = {g} at h; simp [build,h]
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,ne,z,hz,_,r,he,tail⟩
    · exact Or.inl (ih skip)
    · apply Or.inr
      refine ⟨a,ha,b,hb,ne,z,hz,build_subset (ih tail) (Finset.insert_subset_insert _ ?_)⟩
      rw [he]
      exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)

theorem extend_steps {α : Type*} [DecidableEq α] {op : α → α → Finset α}
    {g : α} {k m : ℕ} {s : Finset α} (h : build op g k s) (le : k ≤ m) : build op g m s := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le le
  clear le
  induction d with
  | zero => exact h
  | succ d ih => exact Or.inl ih

theorem goal_nezero : goal ≠ 0 := by decide +kernel

open Classical

theorem packed_bound {r : Samples} {inputs : List W} (nd : inputs.Nodup) {d : ℕ}
    (excluded : search d inputs = false) {g : Paired.Wire} (target : pack r g = goal)
    {av : Finset Paired.Wire} (cover : project (pack r) 0 av ⊆ inputs.toFinset)
    {k : ℕ} (run : build Paired.ops g k av) {saved : ℕ}
    (lost : ∀ s ⊆ av, live Paired.ops g k s → saved ≤ zeroCount (pack r) 0 s) :
    d + 1 + saved ≤ k := by
  obtain ⟨s,sub,lv⟩ := compress run
  have nz : pack r g ≠ 0 := target ▸ goal_nezero
  obtain ⟨l,bound,proj⟩ := project_live Paired.ops extended (pack r) 0
    (fun a b z h h' => extended_simple (pack_preserves r a b z h) h') (pack_preserves r) nz lv
  obtain ⟨t,ts,tl⟩ := compress proj
  have good := (clean_live nz tl).2
  have built := build_subset (live_build good) (ts.trans ((project_subset _ _ sub).trans cover))
  have lower : d < l := by
    by_contra! le
    have yes := search_complete (Or.inl target) d inputs nd (extend_steps built le)
    simp [excluded] at yes
  have loss := lost s sub lv
  omega

theorem lose_essential {r : Samples} {av : Finset Paired.Wire} {goal : Paired.Wire}
    (x y : Paired.Row) (diff : goal x ≠ goal y)
    (only : ∀ a ∈ av, a x ≠ a y → pack r a = 0) {k : ℕ} :
    ∀ s ⊆ av, live Paired.ops goal k s → 1 ≤ zeroCount (pack r) 0 s := by
  intro s sub h
  obtain ⟨a,ha,neq⟩ := Paired.live_distinguishes h x y diff
  exact Finset.card_pos.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,only _ (sub ha) neq⟩⟩

end FullSearch
