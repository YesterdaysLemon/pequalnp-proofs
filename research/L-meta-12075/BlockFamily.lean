import PEqualNP.Outside.L_meta_12072

/-!
Every function in this family restricts to the same five-input problem.
The certificate for that restriction lives in L_meta_12072.
-/
namespace SharedBlock
open PEqualNP.Outside.L_meta_12072
open PEqualNP.Outside.L_meta_12072.Table
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

private def bit (k : Fin 64) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 64) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

set_option maxRecDepth 100000 in
private theorem compileWord (word : W) (nz : word ≠ 0) (no : word ≠ ~~~0)
    (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (word)) :
    ∃ t, (t = ~~~word ∨ t = word) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = word := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim (nz zero)
    · exact False.elim (no ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK (k : Fin 64) : step (w.map (bit k)) g = (w ++ [z]).map (bit k) :=
      action_spec w g (hg g (by simp)) k
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (word) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩


/-- Sample the half of the truth table on which the sixth original input is true. -/
def fixedRows := sampleRow 0x7de75c6da6585d65544d24503ce34c2ca2481c61440c2040

def lowRow (j : Fin 32) : Fin 64 := ⟨j.val, by omega⟩
def highRow (j : Fin 32) : Fin 64 := ⟨j.val + 32, by omega⟩

/-- The sixth input is essential in this pair, and the signed restriction costs nine. -/
theorem restrictedLower (word : W) (j : Fin 32)
    (diff : atRow word (lowRow j) ≠ atRow word (highRow j))
    (fixed : act fixedRows word = Block.y)
    (k : ℕ) (run : build raw word k basis.toFinset) : 10 ≤ k := by
  have onlySix : ∀ i : Fin 32, basis.all (fun w =>
      (atRow w (lowRow i) == atRow w (highRow i)) || (w == 0xffffffff00000000)) = true := by
    decide +kernel
  exact essential_sample (v := 0xffffffff00000000) fixedRows (lowRow j) (highRow j)
    diff (onlySix j) (by decide +kernel) fixed (by decide +kernel) (by decide +kernel)
    (Block.lower (Block.startDebts Clique.lower)) k run

theorem binaryLower (f : (Fin 6 → Bool) → Bool) (word : W) (j : Fin 32)
    (sample : ∀ r : Fin 64, f (fun i => (inputs.getD i.val 0)[r.val]) = word[r.val])
    (diff : atRow word (lowRow j) ≠ atRow word (highRow j))
    (zero : word[0] = false) (fixed : act fixedRows word = Block.y)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = f x) :
    10 ≤ binaryCost gs := by
  have width : inputs.length = 6 := rfl
  have init : ∀ u ∈ inputs, holds basis.toFinset u := by
    intro u hu
    have witnesses : ∀ w ∈ inputs, w ∈ basis.toFinset ∨ ~~~w ∈ basis.toFinset := by
      intro w hw
      simp only [inputs,List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with h | h | h | h | h | h <;> subst w <;> decide +kernel
    rcases witnesses u hu with a | a
    · exact .inr (.inr ⟨u,a,.inl rfl⟩)
    · exact .inr (.inr ⟨~~~u,a,.inr (by simp)⟩)
  have evaluate (k : Fin 64) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (word) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi _
        have hlt : i < inputs.length := by simpa only [width, List.length_ofFn] using hi
        simp only [List.getElem_ofFn,List.getElem_map,x,List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt,Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (word)
    rw [← same,he]
    exact sample k

  have nz : word ≠ 0 := by
    rintro rfl
    apply diff
    simp [atRow]
  have no : word ≠ ~~~0 := by
    rintro rfl
    exact (by decide : (~~~(0 : W))[0] ≠ false) zero
  obtain ⟨u,hu,run⟩ := compileWord word nz no gs o hg inputs basis.toFinset init evaluate
  rcases hu with h | h <;> rw [h] at run
  · obtain ⟨s,sub,hr⟩ := compress run
    obtain ⟨w,hw,on⟩ := live_separates (fun w : W => w[0] = true)
      (by simp [zero] : (~~~word)[0] = true) (fun _ _ _ h => source_zero h) hr
    have none : basis.all (fun w => !w[0]) = true := by decide +kernel
    have noSource := List.all_eq_true.mp none w (List.mem_toFinset.mp (sub hw))
    simp [on] at noSource
  · exact restrictedLower word j diff fixed _ run

/-- An eleven-gate monotone witness is sufficient for every member of this family. -/
theorem comparison (f : (Fin 6 → Bool) → Bool) (word : W) (j : Fin 32)
    (sample : ∀ r : Fin 64, f (fun i => (inputs.getD i.val 0)[r.val]) = word[r.val])
    (diff : atRow word (lowRow j) ≠ atRow word (highRow j))
    (zero : word[0] = false) (fixed : act fixedRows word = Block.y)
    (witness : ∃ D : Circuit, Monotone2 D ∧ D.size ≤ 11 ∧
      ∀ x : Fin 6 → Bool, D.eval (List.ofFn x) = f x)
    (s : ℕ) (h : HasCircuitSize 6 f s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = f x := by
  obtain ⟨C, fits, size, computes⟩ := h
  by_cases has : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g,hm,op⟩ := has
    have less : (C.gates.filter isBinary).length < C.gates.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨g,hm,by simp [isBinary,op]⟩
    have count := binaryLower f word j sample diff zero fixed C.gates C.output (fun g hg => fits g hg) computes
    change 10 ≤ (C.gates.filter isBinary).length at count
    obtain ⟨D,ok,budget,correct⟩ := witness
    refine ⟨D,ok,?_,correct⟩
    change C.gates.length ≤ s at size
    omega
  · refine ⟨C,?_,size,computes⟩
    intro g hm
    obtain ⟨ops',ar⟩ := fits g hm
    refine ⟨?_,ar⟩
    change g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not at ops'
    change g.op = GateOp.and ∨ g.op = GateOp.or
    rcases ops' with a | b | n
    · exact .inl a
    · exact .inr b
    · exact (has ⟨g,hm,n⟩).elim


/-- The low five bits are the ordinary row number. The last input is explicit. -/
def assignment (row : Fin 32) (last : Bool) (i : Fin 6) : Bool :=
  if i.val = 5 then last else row.val.testBit i.val

def encoded (r : Fin 64) (i : Fin 6) : Bool := (inputs.getD i.val 0)[r.val]

/-- A function in this family agrees with the stated cofactor at x₅ = true.
    One pair of its ordinary input rows witnesses dependence on x₅. -/
theorem sharedCofactor (f : (Fin 6 → Bool) → Bool)
    (high : ∀ x, x 5 = true → f x = Table.target x)
    (essential : ∃ z : Fin 32, f (assignment z true) ≠ f (assignment z false))
    (witness : ∃ D : Circuit, Monotone2 D ∧ D.size ≤ 11 ∧
      ∀ x : Fin 6 → Bool, D.eval (List.ofFn x) = f x)
    (s : ℕ) (h : HasCircuitSize 6 f s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = f x := by
  let word := fromRows (fun i => f (encoded i))
  have value (r : Fin 64) : atRow word r = f (encoded r) := read_fromRows _ _
  have pairing : ∀ z : Fin 32, ∃ j : Fin 32,
      encoded (lowRow j) = assignment z true ∧ encoded (highRow j) = assignment z false := by
    decide +kernel
  obtain ⟨z,diff⟩ := essential
  obtain ⟨j,lo,hi⟩ := pairing z
  apply comparison f word j (fun r => (value r).symm) _ _ _ witness s h
  · rwa [value,value,lo,hi]
  · change atRow word 0 = false
    rw [value,high _ (by decide +kernel)]
    decide +kernel
  · apply rows_ext
    intro i
    have on : ∀ r : Fin 64, encoded (fixedRows r) 5 = true := by decide +kernel
    have cofactor : ∀ r : Fin 64, Table.target (encoded (fixedRows r)) = atRow Block.y r := by
      decide +kernel
    rw [act_at,value,high _ (on i)]
    exact cofactor i

end SharedBlock
