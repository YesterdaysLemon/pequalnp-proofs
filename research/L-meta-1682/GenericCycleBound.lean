import PEqualNP.Defs
import PEqualNP.MetaComplexity.L106
import PEqualNP.MetaComplexity.Helpers.PermInputs
import PEqualNP.MetaComplexity.Helpers.LowMergeWires

namespace GenericCycleBound

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

abbrev Bits (n : ℕ) := Fin n → Bool

def row {n : ℕ} (S : Finset ℕ) : Bits n := fun i => decide (i.val ∈ S)
def pad {n : ℕ} (x : Bits n) : Bits 26 := fun i => if h : i.val < n then x ⟨i.val,h⟩ else false

theorem padRow {n : ℕ} (S : Finset ℕ) (bounded : ∀ a ∈ S, a < n) :
    pad (row S : Bits n) = row S := by
  funext i
  by_cases h : i.val < n
  · simp [pad, row, h]
  · have miss : i.val ∉ S := fun hi => h (bounded _ hi)
    simp [pad, row, h, miss]

theorem padSnoc {n : ℕ} (x : Bits n) : pad (Fin.snoc x false) = pad x := by
  funext i
  by_cases h : i.val < n
  · have hs : i.val < n+1 := by omega
    simp only [pad, h, hs, dite_true]
    exact Fin.snoc_castSucc (α := fun _ => Bool) false x ⟨i.val,h⟩
  · by_cases hi : i.val = n
    · have hs : i.val < n+1 := by omega
      simp only [pad, h, hs, dite_true, dite_false]
      have hl : (⟨i.val,hs⟩ : Fin (n+1)) = Fin.last n := Fin.ext hi
      rw [hl, Fin.snoc_last]
    · have hs : ¬i.val < n+1 := by omega
      simp [pad, h, hs]

-- Indices 0 through 7 go around an induced eight-cycle. Later vertices each
-- have an earlier neighbor. This theorem only needs the corresponding tests.
theorem descend (f : Bits 26 → Bool)
    (zero : f (row ∅) = false) (start : f (row {0,1}) = true)
    (one : ∀ j < 26, f (row {j}) = false)
    (attach : ∀ k, 8 ≤ k → k < 26 → ∃ j < k, f (row {k,j}) = true)
    (k : ℕ) (lo : 8 ≤ k) (hi : k < 26)
    (h : HasCircuitSize (k+1) (fun x => f (pad x)) (k+2+1)) :
    HasCircuitSize k (fun x => f (pad x)) (k+2) := by
  obtain ⟨j, hj, hpair⟩ := attach k lo hi
  have hsingle := one j (by omega)
  have hd : ∃ x : Bits (k+1), f (pad (Function.update x (Fin.last k) (!x (Fin.last k)))) ≠
      f (pad x) := by
    refine ⟨row {j}, ?_⟩
    have he : Function.update (row {j}) (Fin.last k) (!(row {j} (Fin.last k))) =
        (row {k,j} : Bits (k+1)) := by
      funext i
      by_cases hp : i = Fin.last k
      · subst i
        simp [row, Fin.val_last, Nat.ne_of_gt hj]
      · have hv : i.val ≠ k := fun e => hp (Fin.ext e)
        simp [Function.update_of_ne hp, row, hv]
    rw [he, padRow, padRow, hpair, hsingle]
    · decide
    · simp_all
      omega
    · simp_all
      omega
  have hn : ∃ a b : Bits k, f (pad (Fin.snoc a false)) ≠ f (pad (Fin.snoc b false)) := by
    refine ⟨row ∅, row {0,1}, ?_⟩
    rw [padSnoc, padSnoc, padRow, padRow, zero, start]
    · decide
    · simp_all
      omega
    · simp
  simpa only [padSnoc] using Helpers.gate_elim k (fun x => f (pad x)) false (k+2) hd hn h

def cycle (x : Bits 8) : Prop := ∃ i j : Fin 8, (i.val+1)%8 = j.val ∧ x i = true ∧ x j = true
instance (x : Bits 8) : Decidable (cycle x) := inferInstanceAs (Decidable (∃ _ _, _))

theorem noTwentyEight (f : Bits 26 → Bool)
    (zero : f (row ∅) = false) (start : f (row {0,1}) = true)
    (one : ∀ j < 26, f (row {j}) = false)
    (attach : ∀ k, 8 ≤ k → k < 26 → ∃ j < k, f (row {k,j}) = true)
    (base : ∀ x : Bits 8, f (pad x) = decide (cycle x)) :
    ¬HasCircuitSize 26 f 28 := by
  intro full
  have eq26 : ∀ x : Bits 26, pad x = x := by
    intro x
    funext i
    simp [pad, i.isLt]
  have down : ∀ t, t ≤ 18 → HasCircuitSize (26-t) (fun x => f (pad x)) (26-t+2) := by
    intro t
    induction t with
    | zero =>
      intro _
      simpa [eq26] using full
    | succ t ih =>
      intro ht
      have h := ih (by omega)
      have eqn : 26-t = (26-(t+1))+1 := by omega
      rw [eqn] at h
      exact descend f zero start one attach _ (by omega) (by omega) h
  have last := down 18 (by decide)
  change HasCircuitSize 8 (fun x => f (pad x)) 10 at last
  simp only [base] at last
  have impossible := (L106 8 10 (by decide)).1 last
  omega

def pos (i : Fin 26) : ℕ :=
  [3,6,12,24,48,96,192,129,258,520,1152,2050,4104,8224,16640,49152,81920,
   131076,393216,524304,1048832,2097664,4194368,8388609,16777220,33554433].getD i 0
def neg (t : Fin 11) : ℕ :=
  [14680468,17580105,33691170,1148969,5283986,5767717,3162197,26214994,35685450,
   34637988,360618].getD t 0
def parent (i : Fin 26) : ℕ :=
  [0,0,0,0,0,0,0,0,1,3,7,1,3,5,8,14,14,2,17,4,8,9,6,0,2,0].getD i 0
def mask (m : ℕ) : Bits 26 := fun i => m.testBit i

private theorem positiveZero : row {0,1} = mask (pos 0) := by decide
private theorem singletonCover : ∀ i : Fin 26, ∃ t : Fin 11, row {i.val} ≤ mask (neg t) := by decide
private theorem parents : ∀ i : Fin 26, 8 ≤ i.val →
    parent i < i.val ∧ row {i.val,parent i} = mask (pos i) := by decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 80000 in
private theorem cycleTests : ∀ x : Bits 8,
    (cycle x → ∃ i : Fin 26, mask (pos i) ≤ pad x) ∧
    (¬cycle x → ∃ t : Fin 11, pad x ≤ mask (neg t)) := by decide

theorem testBound (f : Bits 26 → Bool) (mono : Monotone f)
    (yes : ∀ i, f (mask (pos i)) = true) (no : ∀ t, f (mask (neg t)) = false) :
    ¬HasCircuitSize 26 f 28 := by
  have reject {x y : Bits 26} (hxy : x ≤ y) (hy : f y = false) : f x = false := by
    cases hx : f x with
    | false => rfl
    | true =>
      have bad := Bool.le_iff_imp.mp (mono hxy) hx
      simp [hy] at bad
  apply noTwentyEight f
  · apply reject (y := mask (neg 0)) _ (no 0)
    intro i
    simp [row]
  · rw [positiveZero, yes]
  · intro j hj
    obtain ⟨t,ht⟩ := singletonCover ⟨j,hj⟩
    exact reject ht (no t)
  · intro k lo hi
    let i : Fin 26 := ⟨k,hi⟩
    obtain ⟨hj,he⟩ := parents i lo
    exact ⟨parent i,hj,he ▸ yes i⟩
  · intro x
    by_cases c : cycle x
    · obtain ⟨i,h⟩ := (cycleTests x).1 c
      simpa [c] using Bool.le_iff_imp.mp (mono h) (yes i)
    · obtain ⟨t,h⟩ := (cycleTests x).2 c
      simpa [c] using reject h (no t)

-- Convert each original project input index into the cycle-first numbering.
def rank (i : Fin 26) : Fin 26 :=
  ([0,2,4,8,9,6,15,10,18,11,12,13,16,1,3,5,14,7,17,19,20,21,22,23,24,25] :
    List (Fin 26)).getD i 0

abbrev inc (p w : Fin 13) : Prop :=
  ∃ d ∈ ({0,1,3,9} : Finset (Fin 13)), p = w+d
abbrev misses (P : Finset (Fin 13)) (w : Fin 13) : Prop := ∀ p ∈ P, ¬inc p w
abbrev closed (P : Finset (Fin 13)) : Prop :=
  ∀ v : Fin 13, v ∉ P → ∃ w, misses P w ∧ inc v w
abbrev generic (P : Finset (Fin 13)) : Prop :=
  ¬(∃ w, ∀ p ∈ P, inc p w) ∧ ¬(∃ v, ∀ w, misses P w → inc v w)

def edgeInput (p w : Fin 13) : Bits 26 :=
  fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 w)
def falseInput (P : Finset (Fin 13)) : Bits 26 :=
  fun i => decide ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨
    ∃ w : Fin 13, i = Fin.natAdd 13 w ∧ misses P w)

def flag (i : Fin 26) : Fin 13 × Fin 13 :=
  ([(0,0),(1,0),(1,1),(2,1),(2,2),(5,2),(5,4),(0,4),(3,0),(4,1),(7,4),
    (9,0),(10,1),(11,2),(3,3),(6,3),(12,3),(1,5),(8,5),(2,6),(3,7),(4,8),
    (5,9),(0,10),(1,11),(0,12)] : List (Fin 13 × Fin 13)).getD i (0,0)
def pts (t : Fin 11) : Finset (Fin 13) :=
  let m := ([14,289,1168,4673,2116,19,39,52,224,578,4416] : List ℕ).getD t 0
  Finset.univ.filter (fun p : Fin 13 => m.testBit p)

private theorem positiveGeometry : ∀ i, inc (flag i).1 (flag i).2 ∧
    mask (pos i) ∘ rank = edgeInput (flag i).1 (flag i).2 := by decide

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 20000 in
set_option synthInstance.maxSize 2000 in
private theorem negativeGeometry : ∀ t, closed (pts t) ∧ generic (pts t) ∧
    mask (neg t) ∘ rank = falseInput (pts t) := by
  unfold closed generic misses inc
  decide

private theorem readBit {n : ℕ} (x : Bits n) (i : ℕ) (h : i < n) :
    (List.ofFn x).getD i false = x ⟨i,h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

private theorem evalMono (n : ℕ) (C : Circuit) (hm : Monotone2 C) : Monotone (circuitFun n C) := by
  intro a b hab
  apply Bool.le_iff_imp.mpr
  have hc : IsMonotoneCircuit C := fun g hg => (hm g hg).1
  apply LowMergeProof.wires_mono C hc _ _ (by simp) _ C.output
  intro i hi
  by_cases h : i < n
  · rw [readBit _ i h] at hi ⊢
    exact Bool.le_iff_imp.mp (hab ⟨i,h⟩) hi
  · simp [List.getD_eq_getElem?_getD, h] at hi

theorem unrestrictedLowerBound (C : Circuit) (hm : Monotone2 C)
    (positive : ∀ p w, inc p w → circuitFun 26 C (edgeInput p w) = true)
    (negative : ∀ P, closed P → generic P → circuitFun 26 C (falseInput P) = false) :
    29 ≤ C.size := by
  by_contra! small
  let f : Bits 26 → Bool := fun x => circuitFun 26 C (x ∘ rank)
  have mono : Monotone f := by
    intro a b hab
    exact evalMono 26 C hm (fun i => hab (rank i))
  have yes (i) : f (mask (pos i)) = true := by
    obtain ⟨he,hr⟩ := positiveGeometry i
    change circuitFun 26 C (mask (pos i) ∘ rank) = true
    rw [hr]
    exact positive _ _ he
  have no (t) : f (mask (neg t)) = false := by
    obtain ⟨hc,hg,hr⟩ := negativeGeometry t
    change circuitFun 26 C (mask (neg t) ∘ rank) = false
    rw [hr]
    exact negative _ hc hg
  have hsize : HasCircuitSize 26 (circuitFun 26 C) 28 := by
    refine ⟨C, ?_, by omega, fun _ => rfl⟩
    intro g hg
    obtain ⟨hop,hlen⟩ := hm g hg
    refine ⟨?_, hlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    tauto
  exact testBound f mono yes no (Helpers.PermInputs.relabel_size rank _ 28 hsize)

abbrev adjacent (i j : Fin 26) : Prop :=
  ∃ p w : Fin 13, inc p w ∧
    ((i = Fin.castAdd 13 p ∧ j = Fin.natAdd 13 w) ∨
     (j = Fin.castAdd 13 p ∧ i = Fin.natAdd 13 w))

def pairMasks (k : Fin 25) : ℕ :=
  [7405575,59244600,192832,33885824,12853396,17859153,4737289,3019784,16852260,
   39878850,9572870,34629728,8504192,824337,23199820,34278402,10514592,1849360,
   13107482,6570121,17908257,25559564,3735587,35816514,5572613].getD k 0
def pairPts (k : Fin 25) : Finset (Fin 13) :=
  Finset.univ.filter fun p : Fin 13 => (pairMasks k).testBit p

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 30000 in
set_option synthInstance.maxSize 2000 in
private theorem pairGeometry : ∀ k, closed (pairPts k) ∧ generic (pairPts k) ∧
    mask (pairMasks k) = falseInput (pairPts k) := by
  unfold closed generic misses inc
  decide

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 30000 in
private theorem pairCovered : ∀ i j : Fin 26, ¬ adjacent i j →
    ∃ k : Fin 25, (pairMasks k).testBit i ∧ (pairMasks k).testBit j := by
  unfold adjacent inc
  decide

theorem exactOnPairs (C : Circuit) (hm : Monotone2 C)
    (positive : ∀ p w, inc p w → circuitFun 26 C (edgeInput p w) = true)
    (negative : ∀ P, closed P → generic P → circuitFun 26 C (falseInput P) = false)
    (i j : Fin 26) :
    circuitFun 26 C (fun k => decide (k = i ∨ k = j)) = true ↔ adjacent i j := by
  constructor
  · intro hp
    by_contra hn
    obtain ⟨k,hi,hj⟩ := pairCovered i j hn
    obtain ⟨hc,hg,hr⟩ := pairGeometry k
    have sub : (fun z : Fin 26 => decide (z = i ∨ z = j)) ≤ mask (pairMasks k) := by
      intro z
      apply Bool.le_iff_imp.mpr
      intro hz
      rcases decide_eq_true_iff.mp hz with rfl | rfl
      · exact hi
      · exact hj
    have h := Bool.le_iff_imp.mp (evalMono 26 C hm sub) hp
    rw [hr, negative _ hc hg] at h
    contradiction
  · rintro ⟨p,w,he,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
    · exact positive p w he
    · have swap : (fun k : Fin 26 => decide (k = Fin.natAdd 13 w ∨ k = Fin.castAdd 13 p)) =
          edgeInput p w := by
        funext k
        by_cases hp : k = Fin.castAdd 13 p <;> by_cases hw : k = Fin.natAdd 13 w <;>
          simp [edgeInput, hp, hw]
      rw [swap]
      exact positive p w he

end GenericCycleBound
