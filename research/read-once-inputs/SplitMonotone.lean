import SplitCircuits
import PairedExact

namespace Paired.Split
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def mono (keys : List Coord) (f : Wire) (k : ℕ) :=
  ∃ C : Circuit, Monotone2 C ∧ C.size ≤ k ∧ ∀ x : Row, C.eval (keys.map x) = f x

-- In the enlarged input list q is first. The new gate comes immediately after the primary inputs.
def newIndex (n v i : ℕ) : ℕ := if i < n then (if i = v then n+1 else i+1) else i+2
def mapGate (n v : ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map (newIndex n v)⟩
def joining (t : Bool) (v : ℕ) : Gate := ⟨if t then .and else .or,[v+1,0]⟩
def rewire (n v : ℕ) (t : Bool) (C : Circuit) : Circuit :=
  ⟨joining t v :: C.gates.map (mapGate n v),newIndex n v C.output⟩

theorem add_eval (keys : List Coord) {p : Coord} (mem : p ∈ keys) (q : Coord) (t : Bool) (x : Row) :
    Formula.applyGate ((q::keys).map x) (joining t (keys.idxOf p)) =
      (q::keys).map x ++ [join t (x p) (x q)] := by
  have bd := List.idxOf_lt_length_of_mem mem
  have read : (keys.map x).getD (keys.idxOf p) false = x p := by
    rw [List.getD_eq_getElem _ _ (by simpa using bd),List.getElem_map,List.getElem_idxOf]
  have next : ((q::keys).map x).getD (keys.idxOf p + 1) false = x p := by
    change (keys.map x).getD (keys.idxOf p) false = x p
    exact read
  have first : ((q::keys).map x).getD 0 false = x q := rfl
  unfold Formula.applyGate
  congr 1
  change [(if t then GateOp.and else .or).eval [((q::keys).map x).getD (keys.idxOf p+1) false,
    ((q::keys).map x).getD 0 false]] = _
  rw [next,first]
  cases t <;> simp [GateOp.eval,join]

theorem index_read (keys : List Coord) (nd : keys.Nodup) {p : Coord} (mem : p ∈ keys)
    (q : Coord) (t : Bool) (x : Row) (tail : List Bool) (i : ℕ) :
    (((q::keys).map x ++ [join t (x p) (x q)]) ++ tail).getD (newIndex keys.length (keys.idxOf p) i) false =
      ((keys.map (subst t p q x)) ++ tail).getD i false := by
  by_cases hi : i < keys.length
  · have a := List.idxOf_lt_length_of_mem mem
    have old : ((keys.map (subst t p q x)) ++ tail).getD i false = subst t p q x keys[i] := by
      rw [List.getD_append _ _ _ _ (by simpa using hi),List.getD_eq_getElem _ _ (by simpa using hi),List.getElem_map]
    rw [old]
    by_cases eq : i = keys.idxOf p
    · subst i
      have val := List.getElem_idxOf a
      rw [show newIndex keys.length (keys.idxOf p) (keys.idxOf p) = keys.length+1 by simp [newIndex,a]]
      rw [List.getD_append _ _ _ _ (by simp)]
      rw [show keys.length+1 = ((q::keys).map x).length by simp]
      simp [subst,val]
    · have ne : keys[i] ≠ p := by
        intro he
        exact eq ((nd.idxOf_getElem i hi).symm.trans (congrArg (fun a => keys.idxOf a) he))
      rw [show newIndex keys.length (keys.idxOf p) i = i+1 by simp [newIndex,hi,eq]]
      rw [List.getD_append _ _ _ _ (by simp; omega),List.getD_append _ _ _ _ (by simp; omega)]
      change (keys.map x).getD i false = subst t p q x keys[i]
      rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getElem_map]
      simp [subst,ne]
  · have hnew : (((q::keys).map x) ++ [join t (x p) (x q)]).length = keys.length+2 := by simp
    have hold : (keys.map (subst t p q x)).length = keys.length := List.length_map ..
    rw [show newIndex keys.length (keys.idxOf p) i = i+2 by simp [newIndex,hi]]
    rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),hnew,hold]
    congr 1
    omega

theorem rewire_eval (keys : List Coord) (nd : keys.Nodup) {p : Coord} (mem : p ∈ keys)
    (q : Coord) (t : Bool) (C : Circuit) (x : Row) :
    (rewire keys.length (keys.idxOf p) t C).eval ((q::keys).map x) =
      C.eval (keys.map (subst t p q x)) := by
  let old := keys.map (subst t p q x)
  let new := (q::keys).map x ++ [join t (x p) (x q)]
  let idx := newIndex keys.length (keys.idxOf p)
  let alter := mapGate keys.length (keys.idxOf p)
  have simulate (gs : List Gate) (tail : List Bool) :
      ∃ suffix : List Bool, Formula.run (gs.map alter) (new++tail) = new++suffix ∧
        Formula.run gs (old++tail) = old++suffix := by
    induction gs generalizing tail with
    | nil => exact ⟨tail,rfl,rfl⟩
    | cons g gs ih =>
      let bit := g.op.eval (g.inputs.map fun i => (old++tail).getD i false)
      obtain ⟨s,he,ho⟩ := ih (tail++[bit])
      refine ⟨s,?_,?_⟩
      · change Formula.run (gs.map alter) (Formula.applyGate (new++tail) (alter g)) = _
        have step : Formula.applyGate (new++tail) (alter g) = new++(tail++[bit]) := by
          simp only [Formula.applyGate,alter,mapGate,List.map_map,List.append_assoc]
          congr 3
          apply congrArg g.op.eval
          apply List.map_congr_left
          intro i _
          exact index_read keys nd mem q t x tail i
        rwa [step]
      · change Formula.run gs ((old++tail)++[bit]) = _
        rwa [List.append_assoc]
  obtain ⟨s,hn,ho⟩ := simulate C.gates []
  simp only [List.append_nil] at hn ho
  change (Formula.run (C.gates.map alter) (Formula.applyGate ((q::keys).map x)
    (joining t (keys.idxOf p)))).getD (idx C.output) false = (Formula.run C.gates old).getD C.output false
  rw [add_eval keys mem q t x,show (q::keys).map x ++ [join t (x p) (x q)] = new from rfl,hn,ho]
  exact index_read keys nd mem q t x s C.output

theorem mono_split {keys : List Coord} (nd : keys.Nodup) {f : Wire} {p : Coord} (mem : p ∈ keys)
    (q : Coord) (t : Bool) {k : ℕ} (h : mono keys f k) : mono (q::keys) (split f t p q) (k+1) := by
  obtain ⟨C,ok,bd,ev⟩ := h
  refine ⟨rewire keys.length (keys.idxOf p) t C,?_,?_,?_⟩
  · intro g hg
    rcases List.mem_cons.mp hg with rfl | old
    · cases t <;> simp [joining]
    · obtain ⟨oldGate,hmem,eq⟩ := List.mem_map.mp old
      subst g
      exact ⟨(ok oldGate hmem).1,by simpa [mapGate] using (ok oldGate hmem).2⟩
  · simpa [rewire,Circuit.size] using Nat.add_le_add_right bd 1
  · intro x
    exact (rewire_eval keys nd mem q t C x).trans (ev (subst t p q x))

end Paired.Split
