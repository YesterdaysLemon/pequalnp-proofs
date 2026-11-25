import PairedLower
import PEqualNP.Defs.BinaryCircuit

/-! Interface to the project's full binary basis. Unary and constant gates have zero cost. -/
namespace Paired
noncomputable section
open Classical LiveRestriction PEqualNP.MetaComplexity

def value (s : Finset ℕ) (x : Row) : Bool := decide
  ((∀ i ∈ s, x (i,false) = true) ∨ (∃ i ∈ s, x (i,false) = true ∧ x (i,true) = true))

def labels (n : ℕ) : List Coord := (List.range n).flatMap fun i => [(i,false),(i,true)]

@[simp] theorem label_mem (n : ℕ) (p : Coord) : p ∈ labels n ↔ p.1 < n := by
  rcases p with ⟨i,t⟩
  cases t <;> simp [labels]

def physical (x : Row) (p : Coord) : Bool := if p.2 then x p else !x p
def baseline : Row := fun _ => false
def normalize (w : Wire) : Wire := fun x => (w x) ^^ (w baseline)

theorem normalize_physical (p : Coord) : normalize (fun x => physical x p) = input p := by
  funext x
  simp [normalize,physical,baseline,input]
  cases p.2 <;> cases x p <;> rfl

theorem value_complement (s : Finset ℕ) (x : Row) : value s (physical x) = !target s x := by
  by_cases yes : condition s x
  · have ht : target s x = true := decide_eq_true yes
    rw [ht]
    apply decide_eq_false
    rintro (all | ⟨i,hi,ai,bi⟩)
    · obtain ⟨⟨i,hi,hit⟩,_⟩ := yes
      simpa [physical,hit] using all i hi
    · rcases yes.2 i hi with h | h
      · simpa [physical,h] using ai
      · simpa [physical,h] using bi
  · have ht : target s x = false := decide_eq_false yes
    rw [ht]
    apply decide_eq_true
    by_cases hit : ∃ i ∈ s, x (i,false) = true
    · right
      by_contra none
      apply yes
      refine ⟨hit,?_⟩
      intro i hi
      cases a : x (i,false)
      · right
        cases b : x (i,true)
        · rfl
        · exact (none ⟨i,hi,by simp [physical,a],by simp [physical,b]⟩).elim
      · exact Or.inl rfl
    · left
      intro i hi
      cases a : x (i,false)
      · simp [physical,a]
      · exact (hit ⟨i,hi,a⟩).elim

theorem normalize_value (s : Finset ℕ) :
    normalize (fun x => value s (physical x)) = target s := by
  have base : target s baseline = false := by
    apply decide_eq_false
    rintro ⟨⟨_,_,e⟩,_⟩
    contradiction
  funext x
  simp [normalize,value_complement,base]

theorem normalized_op (o : Op) (a b : Wire) :
    normalize (combine o a b) ∈ ops (normalize a) (normalize b) := by
  let f : Op := fun u v => o (u ^^ a baseline) (v ^^ b baseline) ^^ o (a baseline) (b baseline)
  apply ops_spec.mpr
  refine ⟨f,by simp [f],?_⟩
  funext x
  simp [f,combine,normalize]

def both (o : Op) : Bool :=
  ((o false false != o true false) || (o false true != o true true)) &&
    ((o false false != o false true) || (o true false != o true true))

theorem unary_of_not_both (o : Op) (h : both o = false) :
    (∀ a b, o a b = o a false) ∨ (∀ a b, o a b = o false b) := by
  by_cases eq : o false false = o false true ∧ o true false = o true true
  · left; intro a b; cases a <;> cases b <;> simp [eq.1,eq.2]
  · right
    have eq' : o false false = o true false ∧ o false true = o true true := by
      cases h₀ : o false false <;> cases h₁ : o false true <;> cases h₂ : o true false <;>
        cases h₃ : o true true <;> simp_all [both]
    intro a b; cases a <;> cases b <;> simp [eq'.1,eq'.2]

theorem normalized_unary (f : Bool → Bool) (w : Wire) :
    normalize (fun x => f (w x)) = zero ∨ normalize (fun x => f (w x)) = normalize w := by
  by_cases e : f false = f true
  · left; funext x
    cases h : w x <;> cases b : w baseline <;> simp [normalize,zero,h,b,e]
  · right; funext x
    cases h₀ : f false <;> cases h₁ : f true <;> cases h : w x <;> cases b : w baseline <;>
      simp_all [normalize]

def active (av : Finset Wire) (w : Wire) : Prop := normalize w = zero ∨ normalize w ∈ av
def readGate (ws : List Wire) (g : BinaryGate) : Wire :=
  combine g.op (ws.getD g.left zero) (ws.getD g.right zero)
def bitStep (v : List Bool) (g : BinaryGate) := v ++ [g.op (v.getD g.left false) (v.getD g.right false)]
def atRow (x : Row) (w : Wire) := w x
def cost (C : BinaryCircuit) := (C.gates.filter fun g => both g.op).length

theorem read_at (ws : List Wire) (i : ℕ) (x : Row) :
    (ws.map (atRow x)).getD i false = atRow x (ws.getD i zero) := by
  by_cases h : i < ws.length
  · simp [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD,List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h),atRow,zero]

theorem active_read {ws : List Wire} {av : Finset Wire}
    (ha : ∀ w ∈ ws, active av w) (i : ℕ) : active av (ws.getD i zero) := by
  by_cases h : i < ws.length
  · exact ha _ (by simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

theorem active_unary {av : Finset Wire} {a b : Wire} (o : Op) (h : both o = false)
    (ha : active av a) (hb : active av b) : active av (combine o a b) := by
  rcases unary_of_not_both o h with left | right
  · have eq : combine o a b = fun x => o (a x) false := funext fun x => left _ _
    rw [eq]
    rcases normalized_unary (fun t => o t false) a with z | same
    · exact .inl z
    · unfold active; rw [same]; exact ha
  · have eq : combine o a b = fun x => o false (b x) := funext fun x => right _ _
    rw [eq]
    rcases normalized_unary (o false) b with z | same
    · exact .inl z
    · unfold active; rw [same]; exact hb

theorem compile (gs : List BinaryGate) (out : ℕ) (ws : List Wire) (av : Finset Wire)
    (ha : ∀ w ∈ ws, active av w) (goal : Wire) (nz : goal ≠ zero)
    (eq : normalize (fun x => (gs.foldl bitStep (ws.map (atRow x))).getD out false) = goal) :
    build ops goal (gs.filter fun g => both g.op).length av := by
  induction gs generalizing ws av with
  | nil =>
    have e : normalize (ws.getD out zero) = goal := by simpa only [List.foldl_nil,read_at,atRow] using eq
    rcases active_read ha out with z | mem
    · exact (nz (e.symm.trans z)).elim
    · exact e ▸ mem
  | cons g gs ih =>
    let a := ws.getD g.left zero
    let b := ws.getD g.right zero
    let w := readGate ws g
    have hz : normalize w ∈ ops (normalize a) (normalize b) := normalized_op ..
    have e : normalize (fun x => (gs.foldl bitStep ((ws ++ [w]).map (atRow x))).getD out false) =
        goal := by
      simpa only [List.foldl_cons,bitStep,List.map_append,List.map_cons,List.map_nil,
        read_at,atRow,readGate,w,combine] using eq
    have ha' : active av a := active_read ha _
    have hb' : active av b := active_read ha _
    have skip (al : active av w) := ih (ws ++ [w]) av
      (by simpa only [List.mem_append,List.mem_singleton,or_imp,forall_and] using
            (show ∀ v, (v ∈ ws → active av v) ∧ (v = w → active av v) from
              fun v => ⟨ha v,fun eq => eq ▸ al⟩)) e
    cases depends : both g.op
    · simpa [List.filter_cons,depends] using skip (active_unary g.op depends ha' hb')
    · simp only [List.filter_cons,depends,ite_true,List.length_cons]
      by_cases trivial : normalize a = zero ∨ normalize b = zero ∨ normalize a = normalize b
      · apply Or.inl
        apply skip
        rcases op_simple hz trivial with z | left | right
        · exact .inl z
        · unfold active; rw [left]; exact ha'
        · unfold active; rw [right]; exact hb'
      · push Not at trivial
        refine Or.inr ⟨normalize a,ha'.resolve_left trivial.1,normalize b,
          hb'.resolve_left trivial.2.1,trivial.2.2,normalize w,hz,?_⟩
        apply ih (ws ++ [w]) _ _ e
        intro v hv
        rcases List.mem_append.mp hv with old | last
        · exact (ha v old).imp_right (Finset.mem_insert_of_mem)
        · have ve := List.mem_singleton.mp last
          exact .inr (ve ▸ Finset.mem_insert_self ..)

theorem circuit_lower {n : ℕ} (hn : 2 ≤ n) (C : BinaryCircuit)
    (computes : ∀ x : Row, C.eval ((labels n).map x) = value (Finset.range n) x) :
    3 * n ≤ cost C + 2 := by
  let s := Finset.range n
  let ws : List Wire := (labels n).map fun p x => physical x p
  have init : ∀ w ∈ ws, active (bank s) w := by
    intro w hw
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hw
    right; rw [normalize_physical]
    exact primary_mem (Finset.mem_range.mpr ((label_mem n p).mp hp))
  have agree : (fun x => (C.gates.foldl bitStep (ws.map (atRow x))).getD C.output false) =
      fun x => value s (physical x) := by
    funext x
    have rows : ws.map (atRow x) = (labels n).map (physical x) := by
      simp only [ws,List.map_map]
      rfl
    rw [rows]
    exact computes (physical x)
  have nz : target s ≠ zero := target_nonzero ⟨0,Finset.mem_range.mpr (by omega)⟩
  have run := compile C.gates C.output ws (bank s) init (target s) nz
    ((congrArg normalize agree).trans (normalize_value s))
  simpa [cost,s] using binary_lower s (by simpa [s] using hn) run

end
end Paired
