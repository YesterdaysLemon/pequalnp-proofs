import FullProjection

namespace FullSearch.Six
open LiveRestriction PEqualNP.MetaComplexity
abbrev F := (Fin 6 → Bool) → Bool

def primary (i : Fin 6) : Paired.Wire := Paired.input (i.val,false)
def primaries : List Paired.Wire := List.ofFn primary
def view (x : Paired.Row) (i : Fin 6) : Bool := x (i.val,false)
def liftRow (x : Fin 6 → Bool) : Paired.Row := fun p => x ⟨p.1 % 6, Nat.mod_lt _ (by decide)⟩
def fromArray (rows : Array ℕ) : Samples := fun j p => (rows[j.val]?.getD 0).testBit p.1
def insertOne (atBit v : ℕ) : ℕ := v % 2^atBit + 2^atBit + (v / 2^atBit) * 2^(atBit+1)
def reference (t : ℕ) : F := fun x => Nat.testBit t (∑ i : Fin 6, if x i then 2^i.val else 0)

theorem view_lift (x : Fin 6 → Bool) : view (liftRow x) = x := by
  funext i
  unfold view liftRow
  congr 1
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

theorem normalized_diff {f : Paired.Wire} {x y : Paired.Row} (e : f x ≠ f y) :
    Paired.normalize f x ≠ Paired.normalize f y := by
  cases b : f Paired.baseline <;> simp [Paired.normalize,b,e]

theorem pack_normalize (r : Samples) (f : Paired.Wire) : pack r (Paired.normalize f) = pack r f := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  let j : Fin 512 := ⟨i,hi⟩
  change (pack r (Paired.normalize f))[j.val] = (pack r f)[j.val]
  simp only [pack_at,Paired.normalize]
  cases f (r j) <;> cases f (r 0) <;> cases f Paired.baseline <;> rfl

theorem pack_congr (r : Samples) (f g : Paired.Wire) (h : ∀ i, f (r i) = g (r i)) :
    pack r f = pack r g := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  let j : Fin 512 := ⟨i,hi⟩
  change (pack r f)[j.val] = (pack r g)[j.val]
  simp only [pack_at,h]

open Classical

-- Every essential extension of the sampled cofactor pays at least one extra binary gate.
theorem extension_lower (rows : Array ℕ) (inputs : List W) (fixedIndex : Fin 6) (t : ℕ)
    (nd : inputs.Nodup) {d : ℕ} (excluded : search d inputs = false)
    (fixed : ∀ j, view (fromArray rows j) fixedIndex = true)
    (cover : ∀ i, pack (fromArray rows) (primary i) = 0 ∨
                  pack (fromArray rows) (primary i) ∈ inputs)
    (refGoal : pack (fromArray rows) (fun x => reference t (view x)) = goal)
    (f : F) (agrees : ∀ x, x fixedIndex = true → f x = reference t x)
    (essential : ∃ x y, f x ≠ f y ∧ ∀ i ≠ fixedIndex, x i = y i)
    (C : BinaryCircuit) (ev : ∀ x, C.eval (List.ofFn x) = f x) : d + 2 ≤ Paired.cost C := by
  let r := fromArray rows
  let g : Paired.Wire := fun x => f (view x)
  obtain ⟨x,y,diff,same⟩ := essential
  have ed : Paired.normalize g (liftRow x) ≠ Paired.normalize g (liftRow y) := by
    apply normalized_diff
    simpa [g,view_lift] using diff
  have nz : Paired.normalize g ≠ Paired.zero := by
    intro e
    rw [e] at ed
    exact ed rfl
  have init : ∀ w ∈ primaries, Paired.active primaries.toFinset w := by
    intro w hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    have he : Paired.normalize (primary i) = primary i := by
      funext u
      simp [Paired.normalize,Paired.baseline,primary,Paired.input]
    right
    rw [he]
    exact List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨i,rfl⟩)
  have eq : (fun u => (C.gates.foldl Paired.bitStep (primaries.map (Paired.atRow u))).getD C.output false) = g := by
    funext u
    have map : primaries.map (Paired.atRow u) = List.ofFn (view u) := by
      simp [primaries,primary,Paired.input,Paired.atRow,view]
    rw [map]
    exact ev (view u)
  have run := Paired.compile C.gates C.output primaries primaries.toFinset init (Paired.normalize g) nz
    (congrArg Paired.normalize eq)
  have pg : pack r (Paired.normalize g) = goal :=
    (pack_normalize ..).trans ((pack_congr r g _ (fun j => agrees _ (fixed j))).trans refGoal)
  have initial : project (pack r) 0 primaries.toFinset ⊆ inputs.toFinset := by
    intro w hw
    obtain ⟨nz',h⟩ := Finset.mem_erase.mp hw
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp ha)
    exact List.mem_toFinset.mpr ((cover i).resolve_left nz')
  have c0 : pack r (primary fixedIndex) = 0 := by
    apply BitVec.eq_of_getElem_eq
    intro i hi
    let j : Fin 512 := ⟨i,hi⟩
    change (pack r (primary fixedIndex))[j.val] = (0 : W)[j.val]
    rw [pack_at]
    change (view (r j) fixedIndex ^^ view (r 0) fixedIndex) = _
    rw [fixed j,fixed 0]
    simp
  have only : ∀ a ∈ primaries.toFinset, a (liftRow x) ≠ a (liftRow y) → pack r a = 0 := by
    intro a ha da
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp ha)
    by_cases e : i = fixedIndex
    · exact e ▸ c0
    · exfalso; apply da
      change view (liftRow x) i = view (liftRow y) i
      rw [view_lift,view_lift]
      exact same i e
  exact packed_bound nd excluded pg initial run (lose_essential _ _ ed only)

end FullSearch.Six
