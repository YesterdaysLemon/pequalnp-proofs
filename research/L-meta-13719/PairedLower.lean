import PairedSemantics

namespace Paired
noncomputable section
open Classical LiveRestriction

def mate (p : Coord) : Coord := (p.1,!p.2)

theorem mate_ne (p : Coord) : mate p ≠ p := by
  rcases p with ⟨i,t⟩
  cases t <;> simp [mate]

theorem full_bank {s : Finset ℕ} (hs : 2 ≤ s.card) {k : ℕ} {r : Finset Wire}
    (h : live ops (target s) k r) (sub : r ⊆ bank s) : r = bank s := by
  apply Finset.Subset.antisymm sub
  intro w hw
  obtain ⟨p,hp,rfl⟩ := bank_spec.mp hw
  obtain ⟨x,y,diff,eq,out⟩ := pair_separates hs p (mate p) hp hp (Ne.symm (mate_ne p))
    (fun _ v => v)
  obtain ⟨u,hu,du⟩ := live_distinguishes h x y diff
  obtain ⟨q,_,rfl⟩ := bank_spec.mp (sub hu)
  by_contra no
  have qp : q ≠ p := fun e => no (e ▸ hu)
  by_cases qm : q = mate p
  · exact du (qm ▸ eq)
  · exact du (out q qp qm)

theorem retained {s : Finset ℕ} (hs : 2 ≤ s.card) {p q : Coord}
    (hp : p.1 ∈ s) (hq : q.1 ∈ s) (ne : p ≠ q)
    {z : Wire} (hz : z ∈ ops (input p) (input q)) {k : ℕ} {r : Finset Wire}
    (hr : r ⊆ bank s) (tail : live ops (target s) k (insert z r)) :
    input p ∈ r ∨ input q ∈ r := by
  obtain ⟨o,_,rfl⟩ := ops_spec.mp hz
  obtain ⟨x,y,diff,eq,out⟩ := pair_separates hs p q hp hq ne o
  obtain ⟨w,hw,dw⟩ := live_distinguishes tail x y diff
  rcases Finset.mem_insert.mp hw with rfl | hw
  · exact (dw eq).elim
  · obtain ⟨d,_,rfl⟩ := bank_spec.mp (hr hw)
    by_cases dp : d = p
    · exact .inl (dp ▸ hw)
    by_cases dq : d = q
    · exact .inr (dq ▸ hw)
    · exact (dw (out d dp dq)).elim

theorem ops_swap {a b z : Wire} (h : z ∈ ops a b) : z ∈ ops b a := by
  obtain ⟨o,ho,rfl⟩ := ops_spec.mp h
  exact ops_spec.mpr ⟨fun x y => o y x,ho,rfl⟩

-- The first gate of a live computation leaves at least one of its operands live.
theorem first_retained {s : Finset ℕ} (hs : 2 ≤ s.card) {k : ℕ}
    (h : build ops (target s) k (bank s)) :
    ∃ j, k = j + 1 ∧ ∃ p q : Coord, p.1 ∈ s ∧ q.1 ∈ s ∧ p ≠ q ∧
      ∃ z ∈ ops (input p) (input q), z ∉ bank s ∧ ∃ r : Finset Wire,
        bank s = insert (input p) (insert (input q) r) ∧ input p ∈ r ∧
        live ops (target s) j (insert z r) := by
  obtain ⟨avail,sub,lv⟩ := compress h
  have eq := full_bank hs lv sub
  subst avail
  have ns : bank s ≠ {target s} := by
    intro eq
    have b := congrArg Finset.card eq
    rw [bank_card,Finset.card_singleton] at b
    omega
  cases k with
  | zero => exact (ns lv).elim
  | succ j =>
    rcases first_live lv with done | ⟨a,ha,b,hb,ab,z,hz,hn,r,he,tail⟩
    · exact (ns done).elim
    obtain ⟨p,hp,rfl⟩ := bank_spec.mp ha
    obtain ⟨q,hq,rfl⟩ := bank_spec.mp hb
    have ne : p ≠ q := fun e => ab (congrArg input e)
    have hr : r ⊆ bank s := by
      rw [he]
      exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
    rcases retained hs hp hq ne hz hr tail with keep | keep
    · exact ⟨j,rfl,p,q,hp,hq,ne,z,hz,hn,r,he,keep,tail⟩
    · exact ⟨j,rfl,q,p,hq,hp,ne.symm,z,ops_swap hz,hn,r,
        he.trans (Finset.insert_comm ..),keep,tail⟩

theorem target_nonzero {s : Finset ℕ} (hs : s.Nonempty) : target s ≠ zero := by
  intro h
  let x : Row := fun _ => true
  have t : target s x = true := by
    apply decide_eq_true
    obtain ⟨i,hi⟩ := hs
    exact ⟨⟨i,hi,rfl⟩,fun _ _ => Or.inl rfl⟩
  rw [h] at t
  contradiction

theorem two_zero {i : ℕ} {r : Finset Wire} {a b : Wire}
    (ha : a ∈ r) (hb : b ∈ r) (ne : a ≠ b)
    (az : restrict i a = zero) (bz : restrict i b = zero) :
    2 ≤ zeroCount (restrict i) zero r :=
  Finset.one_lt_card.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,az⟩,
    b,Finset.mem_filter.mpr ⟨hb,bz⟩,ne⟩

-- Restriction deletes the first gate and leaves at least two live wires constant.
theorem save_three {s : Finset ℕ} (hs : 2 ≤ s.card) {k : ℕ}
    (h : build ops (target s) k (bank s)) :
    ∃ i ∈ s, ∃ l, l + 3 ≤ k ∧ build ops (target (s.erase i)) l (bank (s.erase i)) := by
  obtain ⟨j,rfl,p,q,hp,hq,_,z,hz,hn,r,he,keep,tail⟩ := first_retained hs h
  let i := p.1
  let proj := restrict i
  have az : proj (input p) = zero := by simp [proj,i,restrict_input]
  have hr : r ⊆ bank s := by
    rw [he]
    exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
  have nz : proj (target s) ≠ zero := by
    rw [show proj (target s) = target (s.erase i) from restrict_target ..]
    apply target_nonzero
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hp]
    omega
  obtain ⟨l,bound,run⟩ := project_live ops ops proj zero
    (fun a b z mem eq => op_simple (op_preserved i a b z mem) eq) (op_preserved i) nz tail
  have hzsimple := op_simple (op_preserved i _ _ _ hz) (Or.inl az)
  have simple : proj z = zero ∨ proj z = proj (input q) := by
    rcases hzsimple with eq | eq | eq
    · exact .inl eq
    · exact .inl (eq.trans az)
    · exact .inr eq
  have counted : 2 ≤ zeroCount proj zero (insert z r) := by
    by_cases same : q.1 = i
    · have bz : proj (input q) = zero := by simp [proj,restrict_input,same]
      have zz : proj z = zero := simple.elim id (fun e => e.trans bz)
      exact two_zero (Finset.mem_insert_of_mem keep) (Finset.mem_insert_self ..)
        (fun e => hn (e ▸ primary_mem hp)) az zz
    · have other : input (mate p) ∈ r := by
        have mem : input (mate p) ∈ bank s := primary_mem hp
        rw [he] at mem
        rcases Finset.mem_insert.mp mem with eq | mem
        · exact (mate_ne p (input_injective eq)).elim
        rcases Finset.mem_insert.mp mem with eq | mem
        · exact (same (congrArg Prod.fst (input_injective eq)).symm).elim
        · exact mem
      exact two_zero (Finset.mem_insert_of_mem keep) (Finset.mem_insert_of_mem other)
        (fun e => mate_ne p (input_injective e.symm)) az (by simp [i,restrict_input,mate])
  refine ⟨i,hp,l,by omega,?_⟩
  rw [← restrict_target s i]
  apply build_subset run
  apply Finset.Subset.trans _ (project_bank s i)
  intro w hw
  obtain ⟨nonzero,mem⟩ := Finset.mem_erase.mp hw
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp mem
  apply Finset.mem_erase.mpr
  refine ⟨nonzero,?_⟩
  rcases Finset.mem_insert.mp ha with rfl | old
  · rcases simple with e | e
    · exact (nonzero e).elim
    · rw [e]
      exact Finset.mem_image_of_mem _ (primary_mem hq)
  · exact Finset.mem_image_of_mem _ (hr old)

theorem four_gate_base {s : Finset ℕ} (hs : s.card = 2) {k : ℕ}
    (h : build ops (target s) k (bank s)) : 4 ≤ k := by
  obtain ⟨j,rfl,p,q,hp,hq,_,z,_,hn,r,he,keep,tail⟩ := first_retained (by omega) h
  have hcard := live_card tail
  have zr : z ∉ r := fun mem => hn (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem))
  rw [Finset.card_insert_of_notMem zr] at hcard
  have ke : input p ∈ insert (input q) r := Finset.mem_insert_of_mem keep
  rw [Finset.insert_eq_of_mem ke] at he
  have b := bank_card s
  rw [hs,he] at b
  have c := Finset.card_insert_le (input q) r
  omega

theorem binary_lower (s : Finset ℕ) (hs : 2 ≤ s.card) {k : ℕ}
    (h : build ops (target s) k (bank s)) : 3 * s.card ≤ k + 2 := by
  induction s using Finset.strongInductionOn generalizing k
  rename_i s ih
  by_cases base : s.card = 2
  · have b := four_gate_base base h
    omega
  obtain ⟨i,hi,l,b,run⟩ := save_three hs h
  have less := Finset.erase_ssubset hi
  have card := Finset.card_erase_of_mem hi
  have smaller := ih (s.erase i) less (by omega) run
  omega

end
end Paired
