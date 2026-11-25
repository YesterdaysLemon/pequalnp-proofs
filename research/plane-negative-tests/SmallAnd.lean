import PEqualNP.Defs.MetaComplexityLgpMono

namespace SmallAnd
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {n : Nat}
def values (gs : List Gate) (S : Finset (Fin n)) : List Bool :=
  (⟨gs,0⟩ : Circuit).wires (List.ofFn fun i => decide (i ∈ S))
def wire (gs : List Gate) (w : Nat) (S : Finset (Fin n)) : Bool := (values gs S).getD w false
def step (gs : List Gate) (g : Gate) (S : Finset (Fin n)) : Bool :=
  g.op.eval (g.inputs.map fun w => wire gs w S)
theorem append_values (gs : List Gate) (g : Gate) (S : Finset (Fin n)) :
    values (gs++[g]) S = values gs S ++ [step gs g S] := by
  simp [values,step,wire,Circuit.wires,List.foldl_append]
theorem length_values (gs : List Gate) (S : Finset (Fin n)) : (values gs S).length = n+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [values,Circuit.wires]
  | append_singleton l a ih => simp [append_values,ih,Nat.add_assoc]
theorem old_wire (gs : List Gate) (g : Gate) (w : Nat) (h : w < n+gs.length) (S : Finset (Fin n)) :
    wire (gs++[g]) w S = wire gs w S := by
  simp only [wire,append_values]
  exact List.getD_append _ _ _ _ (by simpa [length_values] using h)
theorem last_wire (gs : List Gate) (g : Gate) (S : Finset (Fin n)) :
    wire (gs++[g]) (n+gs.length) S = step gs g S := by
  simp only [wire,append_values,← length_values gs S]
  simp [List.getD_eq_getElem?_getD]
theorem wire_bound {gs : List Gate} {w : Nat} {S : Finset (Fin n)} (h : wire gs w S = true) : w < n+gs.length := by
  by_contra bad
  rw [wire,List.getD_eq_default _ _ (by simp [length_values]; omega)] at h
  cases h

def Active (gs : List Gate) (S : Finset (Fin n)) : Prop :=
  ∃ j g, gs[j]? = some g ∧ g.op = .and ∧ wire gs (n+j) S = true
theorem active_append (gs : List Gate) (g : Gate) (S : Finset (Fin n)) :
    Active (gs++[g]) S ↔ Active gs S ∨ (g.op = .and ∧ step gs g S = true) := by
  constructor
  · rintro ⟨j,k,atj,op,yes⟩
    by_cases h : j < gs.length
    · left
      exact ⟨j,k,by simpa [List.getElem?_append_left h] using atj,op,by simpa [old_wire (n:=n) gs g (n+j) (by omega)] using yes⟩
    · have eq : j=gs.length := by have := wire_bound yes; simp at this; omega
      subst j
      have eqg : g = k := by simpa using atj
      subst k
      exact Or.inr ⟨op,by simpa [last_wire] using yes⟩
  · rintro (⟨j,k,atj,op,yes⟩ | ⟨op,yes⟩)
    · have h : j < gs.length := by have := wire_bound yes; omega
      exact ⟨j,k,by simpa [List.getElem?_append_left h] using atj,op,by simpa [old_wire (n:=n) gs g (n+j) (by omega)] using yes⟩
    · exact ⟨gs.length,g,by simp,op,by simpa [last_wire] using yes⟩

def Primary (gs : List Gate) (S : Finset (Fin n)) : Prop :=
  ∀ w, wire gs w S = true → ∃ i ∈ S, ∀ T : Finset (Fin n), i ∈ T → wire gs w T = true

theorem gather (gs : List Gate) (S : Finset (Fin n)) (p : Primary gs S) (ws : List Nat)
    (h : ∀ w ∈ ws, wire gs w S = true) :
    ∃ T ⊆ S, T.card ≤ ws.length ∧ ∀ U : Finset (Fin n), T ⊆ U → ∀ w ∈ ws, wire gs w U = true := by
  induction ws with
  | nil => exact ⟨∅,by simp,by simp,by simp⟩
  | cons a ws ih =>
    obtain ⟨i,hi,witness⟩ := p a (h a (by simp))
    obtain ⟨T,sub,card,all⟩ := ih (fun w hw => h w (by simp [hw]))
    refine ⟨insert i T,Finset.insert_subset hi sub,?_,?_⟩
    · have := Finset.card_insert_le i T
      simp; omega
    · intro U inc w hw
      rcases List.mem_cons.mp hw with rfl | rest
      · exact witness U (inc (Finset.mem_insert_self i T))
      · exact all U (fun x hx => inc (Finset.mem_insert_of_mem hx)) w rest

theorem invariant (gs : List Gate) (S : Finset (Fin n))
    (mono : Monotone2 (⟨gs,0⟩ : Circuit)) :
    (∃ T ⊆ S, T.card ≤ 2 ∧ Active gs T) ∨ (¬Active gs S ∧ Primary gs S) := by
  induction gs using List.reverseRecOn with
  | nil =>
    right
    refine ⟨by simp [Active],?_⟩
    intro w yes
    have hw : w < n := by simpa using wire_bound yes
    refine ⟨⟨w,hw⟩,?_,?_⟩
    · simpa [wire,values,Circuit.wires,List.getD_eq_getElem?_getD,hw] using yes
    · intro T hT
      simpa [wire,values,Circuit.wires,List.getD_eq_getElem?_getD,hw] using hT
  | append_singleton gs g ih =>
    have old : Monotone2 (⟨gs,0⟩ : Circuit) := by
      intro a ha
      exact mono a (by simp [ha])
    obtain ⟨ops,arity⟩ := mono g (by simp)
    rcases ih old with ⟨T,sub,card,act⟩ | ⟨none,p⟩
    · exact Or.inl ⟨T,sub,card,(active_append ..).mpr (Or.inl act)⟩
    by_cases fires : g.op = .and ∧ step gs g S = true
    · have all : ∀ w ∈ g.inputs, wire gs w S = true := by
        simpa [step,fires.1,GateOp.eval] using fires.2
      obtain ⟨T,sub,card,stable⟩ := gather gs S p g.inputs all
      exact Or.inl ⟨T,sub,card.trans arity,(active_append ..).mpr (Or.inr ⟨fires.1,by
        simpa [step,fires.1,GateOp.eval] using stable T (fun _ h => h)⟩)⟩
    right
    refine ⟨fun h => (active_append ..).mp h |>.elim none fires,?_⟩
    intro w yes
    by_cases hw : w < n+gs.length
    · have e := old_wire gs g w hw
      obtain ⟨i,hi,t⟩ := p w (by simpa [e] using yes)
      exact ⟨i,hi,fun T hT => by simpa [e] using t T hT⟩
    · have eq : w=n+gs.length := by have := wire_bound yes; simp at this; omega
      subst w
      have on : step gs g S = true := by simpa [last_wire] using yes
      have op : g.op = .or := by rcases ops with o | o; exact False.elim (fires ⟨o,on⟩); exact o
      obtain ⟨a,ha,atS⟩ : ∃ a ∈ g.inputs, wire gs a S = true := by simpa [step,op,GateOp.eval] using on
      obtain ⟨i,hi,t⟩ := p a atS
      refine ⟨i,hi,fun T hT => ?_⟩
      rw [last_wire]
      simpa [step,op,GateOp.eval] using (show ∃ a ∈ g.inputs, wire gs a T = true from ⟨a,ha,t T hT⟩)

theorem sparse (C : Circuit) (mono : Monotone2 C) (S : Finset (Fin n)) (active : Active C.gates S) :
    ∃ T ⊆ S, T.card ≤ 2 ∧ Active C.gates T := by
  rcases invariant C.gates S mono with h | h
  · exact h
  · exact False.elim (h.1 active)

theorem mono_wire (gs : List Gate) (ok : Monotone2 (⟨gs,0⟩ : Circuit)) {S T : Finset (Fin n)}
    (sub : S ⊆ T) (w : Nat) (hs : wire gs w S = true) : wire gs w T = true := by
  induction gs using List.reverseRecOn generalizing w with
  | nil =>
    have hw : w < n := by simpa using wire_bound hs
    have mem : (⟨w,hw⟩ : Fin n) ∈ S := by simpa [wire,values,Circuit.wires,List.getD_eq_getElem?_getD,hw] using hs
    simpa [wire,values,Circuit.wires,List.getD_eq_getElem?_getD,hw] using sub mem
  | append_singleton gs g ih =>
    have old : Monotone2 (⟨gs,0⟩ : Circuit) := fun a ha => ok a (by simp [ha])
    by_cases hw : w < n+gs.length
    · rw [old_wire (n:=n) gs g w hw] at hs ⊢
      exact ih old w hs
    · have eq : w=n+gs.length := by have := wire_bound hs; simp at this; omega
      subst w
      rw [last_wire] at hs ⊢
      have kind : g.op = .and ∨ g.op = .or := (ok g (by simp)).1
      rcases kind with op | op
      · simp [step,op,GateOp.eval] at hs ⊢
        exact fun a ha => ih old a (hs a ha)
      · simp [step,op,GateOp.eval] at hs ⊢
        obtain ⟨a,ha,yes⟩ := hs
        exact ⟨a,ha,ih old a yes⟩

theorem mono_active (C : Circuit) (mono : Monotone2 C) {S T : Finset (Fin n)} (h : S ⊆ T)
    (act : Active C.gates S) : Active C.gates T := by
  obtain ⟨j,g,hj,op,yes⟩ := act
  exact ⟨j,g,hj,op,mono_wire C.gates mono h (n+j) yes⟩

/-- For any downward-closed promise, covering all its sets of size at most two suffices. -/
theorem testing (C : Circuit) (mono : Monotone2 C) (Neg : Finset (Fin n) → Prop)
    (down : ∀ S T, Neg S → T ⊆ S → Neg T) (tests : Finset (Finset (Fin n)))
    (valid : ∀ A ∈ tests, Neg A)
    (cover : ∀ T, Neg T → T.card ≤ 2 → ∃ A ∈ tests, T ⊆ A) :
    (∃ S, Neg S ∧ Active C.gates S) ↔ ∃ A ∈ tests, Active C.gates A := by
  constructor
  · rintro ⟨S,neg,act⟩
    obtain ⟨T,sub,bd,yes⟩ := sparse C mono S act
    obtain ⟨A,ha,ext⟩ := cover T (down S T neg sub) bd
    exact ⟨A,ha,mono_active C mono ext yes⟩
  · rintro ⟨A,ha,yes⟩
    exact ⟨A,valid A ha,yes⟩

theorem cover_pairs {V I : Type} [DecidableEq V] [Nonempty I] (sets : I → Finset V)
    (T : Finset V) (card : T.card ≤ 2)
    (pairs : ∀ a ∈ T, ∀ b ∈ T, ∃ i, a ∈ sets i ∧ b ∈ sets i) : ∃ i, T ⊆ sets i := by
  classical
  obtain rfl | ⟨a,ha⟩ := T.eq_empty_or_nonempty
  · exact ⟨Classical.arbitrary I,by simp⟩
  have hrest : (T.erase a).card ≤ 1 := by rw [Finset.card_erase_of_mem ha]; omega
  obtain emp | ⟨b,hb⟩ := (T.erase a).eq_empty_or_nonempty
  · obtain ⟨i,hk,_⟩ := pairs a ha a ha
    refine ⟨i,fun w hw => ?_⟩
    have eq : w=a := by
      by_contra ne
      have mem := Finset.mem_erase.mpr ⟨ne,hw⟩
      rw [emp] at mem
      exact Finset.notMem_empty _ mem
    simpa [eq] using hk
  · obtain ⟨i,ka,kb⟩ := pairs a ha b (Finset.mem_of_mem_erase hb)
    refine ⟨i,fun w hw => ?_⟩
    by_cases eq : w=a
    · simpa [eq] using ka
    · have eqb := (Finset.card_le_one_iff.mp hrest) (Finset.mem_erase.mpr ⟨eq,hw⟩) hb
      simpa [eqb] using kb

noncomputable def probe (T : Finset (Fin n)) : Circuit := ⟨[⟨.and,T.toList.map Fin.val⟩],n⟩

theorem probe_small (T : Finset (Fin n)) (bound : T.card ≤ 2) : Monotone2 (probe T) := by
  intro g hg
  have eq : g = ⟨.and,T.toList.map Fin.val⟩ := by simpa [probe] using hg
  subst g
  simpa using bound

theorem input_wire (u : Fin n) (S : Finset (Fin n)) : wire [] u.val S = decide (u ∈ S) := by
  simp [wire,values,Circuit.wires,List.getD_eq_getElem?_getD,u.isLt]

theorem probe_active (T A : Finset (Fin n)) : Active (probe T).gates A ↔ T ⊆ A := by
  change Active ([]++[⟨.and,T.toList.map Fin.val⟩]) A ↔ _
  rw [active_append]
  simp [Active,step,GateOp.eval,input_wire,Finset.subset_iff]

theorem exact_testing (Neg : Finset (Fin n) → Prop)
    (down : ∀ S T, Neg S → T ⊆ S → Neg T) (tests : Finset (Finset (Fin n)))
    (valid : ∀ A ∈ tests, Neg A) :
    (∀ C : Circuit, Monotone2 C →
       ((∃ S, Neg S ∧ Active C.gates S) ↔ ∃ A ∈ tests, Active C.gates A)) ↔
    (∀ T, Neg T → T.card ≤ 2 → ∃ A ∈ tests, T ⊆ A) := by
  constructor
  · intro all T neg bd
    obtain ⟨A,mem,act⟩ := (all (probe T) (probe_small T bd)).mp ⟨T,neg,(probe_active T T).mpr (by rfl)⟩
    exact ⟨A,mem,(probe_active T A).mp act⟩
  · intro cover C mono
    exact testing C mono Neg down tests valid cover

end SmallAnd
