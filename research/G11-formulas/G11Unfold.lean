import G11Project
import PEqualNP.Defs.TopForm

namespace KWPartition
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership

/-- The gate indices appear once per occurrence in the expanded output formula. -/
inductive Unfold (n : Nat) : List Gate → Nat → Formula (Fin n) → List Nat → Prop where
  | input (v : Fin n) : Unfold n [] v (.var v) []
  | keep {gs w f tr} (p : Unfold n gs w f tr) (g : Gate) : Unfold n (gs++[g]) w f tr
  | meet {gs a b f g u v} (left : Unfold n gs a f u) (right : Unfold n gs b g v) :
      Unfold n (gs++[⟨.and,[a,b]⟩]) (n+gs.length) (.meet f g) (gs.length::(u++v))
  | join {gs a b f g u v} (left : Unfold n gs a f u) (right : Unfold n gs b g v) :
      Unfold n (gs++[⟨.or,[a,b]⟩]) (n+gs.length) (.join f g) (gs.length::(u++v))

theorem bounds {n gs w f tr} (p : Unfold n gs w f tr) :
    w < n+gs.length ∧ (∀ i ∈ tr, i < gs.length) ∧ tr.length = f.gates := by
  induction p with
  | input v => simp [Formula.gates]
  | keep _ _ ih =>
    obtain ⟨h,m,e⟩ := ih
    refine ⟨by simp; omega,fun i hi => ?_,e⟩
    have l := m i hi
    simp; omega
  | meet _ _ hl hr | join _ _ hl hr =>
    obtain ⟨_,left,leq⟩ := hl
    obtain ⟨_,right,req⟩ := hr
    refine ⟨by simp,?_,by simp [Formula.gates,leq,req]⟩
    intro i hi
    simp only [List.mem_cons,List.mem_append] at hi
    rcases hi with rfl | h | h
    · simp
    · have l := left i h; simp; omega
    · have l := right i h; simp; omega

def values (gs : List Gate) (x : List Bool) := (⟨gs,0⟩ : Circuit).wires x
theorem values_append (gs : List Gate) (g : Gate) (x : List Bool) :
    values (gs++[g]) x = values gs x ++ [g.op.eval (g.inputs.map (fun i => (values gs x).getD i false))] := by
  simp [values,Circuit.wires,List.foldl_append]

theorem values_length (gs : List Gate) (x : List Bool) : (values gs x).length = x.length+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [values,Circuit.wires]
  | append_singleton l a ih => simp [values_append,ih,Nat.add_assoc]

theorem evaluates {n gs w f tr} (p : Unfold n gs w f tr) (x : Fin n → Bool) :
    (values gs (List.ofFn x)).getD w false = f.eval x := by
  induction p with
  | input v => simp [values,Circuit.wires,Formula.eval,List.getD_eq_getElem?_getD]
  | @keep gs w _ _ prev g ih =>
    rw [values_append,List.getD_append]
    · exact ih
    · simpa [values_length] using (bounds prev).1
  | @meet gs a b f g _ _ _ _ left right | @join gs a b f g _ _ _ _ left right =>
    have length : (values gs (List.ofFn x)).length = n+gs.length := by simp [values_length]
    rw [values_append,← length]
    simp only [List.getD_eq_getElem?_getD] at left right
    simp [GateOp.eval,Formula.eval,left,right]

def Legal (n : Nat) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∃ a b, a < n+j ∧ b < n+j ∧
    (gs[j] = ⟨.and,[a,b]⟩ ∨ gs[j] = ⟨.or,[a,b]⟩)

theorem complete {n : Nat} (gs : List Gate) (leg : Legal n gs) (w : Nat) (hw : w < n+gs.length) :
    ∃ f tr, Unfold n gs w f tr := by
  induction gs using List.reverseRecOn generalizing w with
  | nil => exact ⟨_,_,Unfold.input ⟨w,by simpa using hw⟩⟩
  | append_singleton gs g ih =>
    have old : Legal n gs := by
      intro j hj
      have bound : j < (gs++[g]).length := by simp; omega
      simpa only [List.getElem_append_left hj] using leg j bound
    by_cases h : w < n+gs.length
    · obtain ⟨f,tr,p⟩ := ih old w h
      exact ⟨f,tr,.keep p g⟩
    · have we : w=n+gs.length := by simp at hw; omega
      obtain ⟨a,b,ha,hb,op⟩ := leg gs.length (by simp)
      simp at op
      obtain ⟨f,u,left⟩ := ih old a ha
      obtain ⟨h,v,right⟩ := ih old b hb
      subst w
      rcases op with rfl | rfl
      · exact ⟨_,_,.meet left right⟩
      · exact ⟨_,_,.join left right⟩

theorem legal_of_ao {n : Nat} {C : Circuit} (h : IsAO2 n C) : Legal n C.gates := by
  obtain ⟨ops,back,arity⟩ := h
  intro j hj
  have mem := List.getElem_mem (l := C.gates) hj
  have kind := ops _ mem
  have two := arity _ mem
  have gate : gateAt C j = C.gates[j] := by
    simp [gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]
  have prev := back j hj
  rw [gate] at prev
  generalize eq : C.gates[j] = g at kind two prev ⊢
  obtain ⟨op,args⟩ := g
  cases args with
  | nil => simp at two
  | cons a tail =>
    cases tail with
    | nil => simp at two
    | cons b rest =>
      cases rest with
      | nil =>
        refine ⟨a,b,prev _ (by simp),prev _ (by simp),?_⟩
        rcases kind with rfl | rfl <;> simp
      | cons c rest => simp at two

theorem trace_bound {n gs w f tr} (p : Unfold n gs w f tr) (nd : tr.Nodup) : f.gates ≤ gs.length := by
  have sub : tr.toFinset ⊆ Finset.range gs.length := fun i hi =>
      Finset.mem_range.mpr ((bounds p).2.1 i (List.mem_toFinset.mp hi))
  have card := Finset.card_le_card sub
  simpa [List.toFinset_card_of_nodup nd,(bounds p).2.2] using card

end KWPartition

namespace G11Game
open KWPartition PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

theorem repeated_gate (proof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (checked : Std.Tactic.BVDecide.LRAT.check proof (KWEncoding.problem game 22) = true)
    (D : Circuit) (ao : IsAO2 11 D) (small : D.size ≤ 21)
    (ev : ∀ x : V → Bool, D.eval (List.ofFn x) = graphFun source ∅ x) :
    ∃ f tr, Unfold 11 D.gates D.output f tr ∧ ¬tr.Nodup := by
  have hit := ev (yes 0)
  have one := (graph_agrees (yes 0)).symm.trans (rows_positive 0)
  have valid : D.output < 11+D.gates.length := by
    by_contra bad
    change (values D.gates (List.ofFn (yes 0))).getD D.output false = _ at hit
    rw [List.getD_eq_default _ _ (by simp [values_length]; omega),one] at hit
    cases hit
  obtain ⟨f,tr,u⟩ := complete D.gates (legal_of_ao ao) D.output valid
  refine ⟨f,tr,u,fun nd => ?_⟩
  have bd := (trace_bound u nd).trans small
  have impossible := (formula_size proof checked 21).mp ⟨f,bd,fun x => (evaluates u x).symm.trans (ev x)⟩
  omega

end G11Game
