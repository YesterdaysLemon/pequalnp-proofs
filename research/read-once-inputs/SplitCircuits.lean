import ReadOnceSplit

namespace Paired.Split
open LiveRestriction PEqualNP.MetaComplexity
noncomputable section
open Classical

-- A circuit in the project's full basis, charging only gates sensitive to both arguments.
def native (keys : List Coord) (f : Wire) (k : ℕ) : Prop :=
  ∃ C : BinaryCircuit, cost C ≤ k ∧ ∀ x : Row, C.eval (keys.map x) = f x

def run (gs : List BinaryGate) (v : List Bool) := gs.foldl bitStep v

theorem run_length (gs : List BinaryGate) (v : List Bool) : (run gs v).length = v.length+gs.length := by
  induction gs generalizing v with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (bitStep v g)).length = _
    rw [ih]
    simp [bitStep]
    omega

theorem run_snoc (gs : List BinaryGate) (g : BinaryGate) (v : List Bool) :
    run (gs ++ [g]) v = bitStep (run gs v) g := by simp [run,List.foldl_append]

def realized (keys : List Coord) (gs : List BinaryGate) (av : Finset Wire) : Prop :=
  ∀ w ∈ av, ∃ i, i < keys.length + gs.length ∧ ∀ x : Row, (run gs (keys.map x)).getD i false = w x

theorem add_wire {keys : List Coord} {gs : List BinaryGate} {av : Finset Wire}
    (ok : realized keys gs av) {a b z : Wire} (ha : a ∈ av) (hb : b ∈ av) (hz : z ∈ ops a b) :
    ∃ g : BinaryGate, realized keys (gs ++ [g]) (insert z av) := by
  obtain ⟨i,_,ei⟩ := ok a ha
  obtain ⟨j,_,ej⟩ := ok b hb
  obtain ⟨o,_,rfl⟩ := ops_spec.mp hz
  let g : BinaryGate := ⟨o,i,j⟩
  refine ⟨g,?_⟩
  intro w hw
  rcases Finset.mem_insert.mp hw with rfl | old
  · refine ⟨keys.length + gs.length,by simp,?_⟩
    intro x
    have len : (run gs (keys.map x)).length = keys.length + gs.length := by simp [run_length]
    rw [run_snoc,← len]
    have left := ei x
    have right := ej x
    simp only [List.getD_eq_getElem?_getD] at left right
    simp [bitStep,g,combine,left,right]
  · obtain ⟨u,bd,ev⟩ := ok w old
    refine ⟨u,by simp; omega,?_⟩
    intro x
    rw [run_snoc,bitStep,List.getD_append _ _ _ _ (by simpa [run_length] using bd)]
    exact ev x

theorem realize_build {s : Finset Wire} {goal : Wire} {k : ℕ} (h : build ops goal k s)
    (keys : List Coord) (gs : List BinaryGate) (ok : realized keys gs s) :
    ∃ tail : List BinaryGate, tail.length ≤ k ∧ ∃ i, i < keys.length + (gs++tail).length ∧
      ∀ x : Row, (run (gs++tail) (keys.map x)).getD i false = goal x := by
  induction k generalizing s gs with
  | zero =>
    obtain ⟨i,bd,ev⟩ := ok goal h
    exact ⟨[],by simp,i,by simpa using bd,by simpa using ev⟩
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,_,z,hz,next⟩
    · obtain ⟨tail,bd,wire,corr⟩ := ih skip gs ok
      exact ⟨tail,by omega,wire,corr⟩
    · obtain ⟨g,inserted⟩ := add_wire ok ha hb hz
      obtain ⟨tail,bd,wire,hi,ev⟩ := ih next (gs++[g]) inserted
      exact ⟨g::tail,by simp; omega,wire,by simpa using hi,by simpa using ev⟩

theorem initial_realized (keys : List Coord) : realized keys [] (primaryBank keys.toFinset) := by
  intro w hw
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hw
  have bd := List.idxOf_lt_length_of_mem (List.mem_toFinset.mp hp)
  refine ⟨keys.idxOf p,by simpa using bd,?_⟩
  intro x
  change (keys.map x).getD _ false = _
  rw [List.getD_eq_getElem _ _ (by simpa using bd),List.getElem_map,List.getElem_idxOf]
  rfl

theorem native_iff (keys : List Coord) (f : Wire) (k : ℕ) (nz : normalize f ≠ zero) :
    native keys f k ↔ feasible keys.toFinset f k := by
  constructor
  · rintro ⟨C,bd,ev⟩
    let ws := keys.map input
    have al : ∀ w ∈ ws, active (primaryBank keys.toFinset) w := by
      intro w hw
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hw
      right
      rw [input_normal]
      exact Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hp)
    have eq : (fun x => (C.gates.foldl bitStep (ws.map (atRow x))).getD C.output false) = f := by
      funext x
      have hws : ws.map (atRow x) = keys.map x := by simp [ws,atRow,input,List.map_map]
      rw [hws]
      exact ev x
    exact steps (compile C.gates C.output ws _ al (normalize f) nz (congrArg normalize eq)) bd
  · intro h
    obtain ⟨gs,bd,i,hi,ev⟩ := realize_build h keys [] (initial_realized keys)
    simp only [List.nil_append] at hi ev
    cases base : f baseline
    · refine ⟨⟨gs,i⟩,(List.length_filter_le ..).trans bd,?_⟩
      intro x
      change (run gs (keys.map x)).getD i false = _
      simpa [normalize,base] using ev x
    · let inv : BinaryGate := ⟨fun a _ => !a,i,i⟩
      refine ⟨⟨gs++[inv],keys.length+gs.length⟩,?_,?_⟩
      · change ((gs++[inv]).filter _).length ≤ k
        simpa [List.filter_append,inv,both] using
          ((List.length_filter_le (fun g : BinaryGate => both g.op) gs).trans bd)
      · intro x
        change (run (gs++[inv]) (keys.map x)).getD _ false = _
        have len : (run gs (keys.map x)).length = keys.length + gs.length := by simp [run_length]
        rw [run_snoc,← len]
        simp [bitStep,inv]
        simpa [normalize,base,List.getD_eq_getElem?_getD] using ev x

theorem native_split_iff (keys : List Coord) {f : Wire} (sup : supported keys.toFinset f)
    {p q : Coord} (hp : p ∈ keys) (fresh : q ∉ keys) (t : Bool) (ess : essential f p) (k : ℕ) :
    native (q::keys) (split f t p q) (k+1) ↔ native keys f k := by
  have hq : q ∉ keys.toFinset := by simpa using fresh
  have hs := fresh_essential sup (List.mem_toFinset.mpr hp) hq t ess
  rw [native_iff _ _ _ (nonzero_of_essential hs),native_iff _ _ _ (nonzero_of_essential ess)]
  simpa only [List.toFinset_cons] using split_iff sup (List.mem_toFinset.mpr hp) hq t ess k

end
end Paired.Split
