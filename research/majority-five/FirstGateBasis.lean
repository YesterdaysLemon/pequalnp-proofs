import SplitCircuits

namespace FirstGate
open Paired Paired.Split LiveRestriction PEqualNP.MetaComplexity
noncomputable section
open Classical

def parity (o : Op) : Bool :=
  (o false false == o true true) && (o false true == o true false) && (o false false != o false true)

def family (all : Bool) (a b : Wire) : Finset Wire :=
  ((Finset.univ : Finset Op).filter fun o => o false false = false ∧
    (all = true ∨ parity o = false)).image (fun o => combine o a b)

theorem member {all : Bool} {a b z : Wire} : z ∈ family all a b ↔
    ∃ o : Op, (o false false = false ∧ (all = true ∨ parity o = false)) ∧ combine o a b = z := by
  simp [family]

theorem included {all : Bool} {a b z : Wire} (h : z ∈ family all a b) : z ∈ Paired.ops a b := by
  obtain ⟨o,⟨base,_⟩,rfl⟩ := member.mp h
  exact ops_spec.mpr ⟨o,base,rfl⟩

theorem relax {all : Bool} {s : Finset Wire} {y : Wire} {k : Nat}
    (h : live (family all) y k s) : live Paired.ops y k s := by
  induction k generalizing s with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,ne,z,hz,hn,r,e,tail⟩
    · exact Or.inl (ih skip)
    · exact Or.inr ⟨a,ha,b,hb,ne,z,included hz,hn,r,e,ih tail⟩

theorem polar (o : Op) (a b : Bool) :
    parity (fun x y => o (x ^^ a) (y ^^ b) ^^ o a b) = parity o := by
  cases a <;> cases b <;> cases h0 : o false false <;> cases h1 : o false true <;>
    cases h2 : o true false <;> cases h3 : o true true <;> simp [parity,h0,h1,h2,h3]

theorem normalize_member {all : Bool} (o : Op) (allow : all = true ∨ parity o = false) (a b : Wire) :
    normalize (combine o a b) ∈ family all (normalize a) (normalize b) := by
  let f : Op := fun u v => o (u ^^ a baseline) (v ^^ b baseline) ^^ o (a baseline) (b baseline)
  apply member.mpr
  refine ⟨f,⟨by simp [f],?_⟩,?_⟩
  · simpa [f,polar] using allow
  · funext x; simp [f,combine,normalize]

theorem compile (all : Bool) (gs : List BinaryGate) (out : ℕ) (ws : List Wire) (av : Finset Wire)
    (ha : ∀ w ∈ ws, active av w) (goal : Wire) (nz : goal ≠ zero)
    (allow : ∀ g ∈ gs, all = true ∨ parity g.op = false)
    (eq : normalize (fun x => (gs.foldl bitStep (ws.map (atRow x))).getD out false) = goal) :
    build (family all) goal (gs.filter fun g => both g.op).length av := by
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
    have hz : normalize w ∈ family all (normalize a) (normalize b) := normalize_member _ (allow g (by simp)) a b
    have rest : ∀ g' ∈ gs, all = true ∨ parity g'.op = false := fun v hv => allow v (List.mem_cons_of_mem _ hv)
    have e : normalize (fun x => (gs.foldl bitStep ((ws ++ [w]).map (atRow x))).getD out false) =
        goal := by
      simpa only [List.foldl_cons,bitStep,List.map_append,List.map_cons,List.map_nil,
        read_at,atRow,readGate,w,combine] using eq
    have ha' : active av a := active_read ha _
    have hb' : active av b := active_read ha _
    have skip (al : active av w) := ih (ws ++ [w]) av
      (by simpa only [List.mem_append,List.mem_singleton,or_imp,forall_and] using
            (show ∀ v, (v ∈ ws → active av v) ∧ (v = w → active av v) from
              fun v => ⟨ha v,fun eq => eq ▸ al⟩)) rest e
    cases depends : both g.op
    · simpa [List.filter_cons,depends] using skip (active_unary g.op depends ha' hb')
    · simp only [List.filter_cons,depends,ite_true,List.length_cons]
      by_cases trivial : normalize a = zero ∨ normalize b = zero ∨ normalize a = normalize b
      · apply Or.inl
        apply skip
        rcases op_simple (included hz) trivial with z | left | right
        · exact .inl z
        · unfold active; rw [left]; exact ha'
        · unfold active; rw [right]; exact hb'
      · push Not at trivial
        refine Or.inr ⟨normalize a,ha'.resolve_left trivial.1,normalize b,
          hb'.resolve_left trivial.2.1,trivial.2.2,normalize w,hz,?_⟩
        apply ih (ws ++ [w]) _ _ rest e
        intro v hv
        rcases List.mem_append.mp hv with old | last
        · exact (ha v old).imp_right (Finset.mem_insert_of_mem)
        · have ve := List.mem_singleton.mp last
          exact .inr (ve ▸ Finset.mem_insert_self ..)

theorem of_circuit {all : Bool} (keys : List Coord) (f : Wire) (C : BinaryCircuit)
    (allow : ∀ g ∈ C.gates, all = true ∨ parity g.op = false)
    (ev : ∀ x : Row, C.eval (keys.map x) = f x) (nz : normalize f ≠ zero) :
    build (family all) (normalize f) (cost C) (primaryBank keys.toFinset) := by
  let ws := keys.map input
  have al : ∀ w ∈ ws, active (primaryBank keys.toFinset) w := by
    intro w hw
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hw
    right; rw [input_normal]
    exact Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hp)
  have eq : (fun x => (C.gates.foldl bitStep (ws.map (atRow x))).getD C.output false) = f := by
    funext x
    have hws : ws.map (atRow x) = keys.map x := by simp [ws,atRow,input,List.map_map]
    rw [hws]
    exact ev x
  exact compile all C.gates C.output ws _ al _ nz allow (congrArg normalize eq)

end
end FirstGate
