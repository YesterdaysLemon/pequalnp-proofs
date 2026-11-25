import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.LowMergeWires

namespace FlagPruning

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)
open PEqualNP.MetaComplexity.LowMergeProof

abbrev Pair (N : ℕ) := Fin N × Fin N
abbrev Bits (N : ℕ) := Fin (N+N) → Bool
def row {N} (e : Pair N) : Bits N := fun k =>
  decide (k = Fin.castAdd N e.1 ∨ k = Fin.natAdd N e.2)
def value {N} (C : Circuit) (w : ℕ) (x : Bits N) : Bool :=
  (C.wires (List.ofFn x)).getD w false
def supported {N} (I : Fin N → Fin N → Prop) (C : Circuit) (j : ℕ) (e : Pair N) :=
  I e.1 e.2 ∧ value C (N+N+j) (row e) = true

inductive Action (N : ℕ)
  | keep | off | pair (e : Pair N)

def Action.gate {N} (a : Action N) (g : Gate) : Gate :=
  match a with
  | .keep => g
  | .off => ⟨.or, []⟩
  | .pair e => ⟨.and, [(Fin.castAdd N e.1).val, (Fin.natAdd N e.2).val]⟩

noncomputable def plan {N} (I : Fin N → Fin N → Prop) (C : Circuit) (j : ℕ) : Action N := by
  classical
  exact if (gateAt C j).op = .and then
    if hz : ∃ e, supported I C j e then
      if hu : ∃ e, supported I C j e ∧ ∀ f, supported I C j f → f = e then
        .pair (Classical.choose hu)
      else .keep
    else .off
  else .keep

def compile {N} (A : ℕ → Action N) (C : Circuit) : Circuit :=
  ⟨List.ofFn (fun j : Fin C.gates.length => (A j).gate C.gates[j]), C.output⟩

@[simp] theorem len {N A C} : (compile (N:=N) A C).gates.length = C.gates.length := by
  simp [compile]

theorem atGate (C : Circuit) {j} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

@[simp] theorem compiledAt {N} (A : ℕ → Action N) (C : Circuit) {j}
    (hj : j < C.gates.length) : gateAt (compile A C) j = (A j).gate (gateAt C j) := by
  rw [atGate _ (by simpa using hj), atGate _ hj]
  simp [compile]

theorem shape {N} (A : ℕ → Action N) (C : Circuit) (hm : Monotone2 C)
    (hb : ReadsBack (N+N) C) : Monotone2 (compile A C) ∧ ReadsBack (N+N) (compile A C) := by
  constructor
  · intro g hg
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
    cases A j with
    | keep => exact hm _ (List.getElem_mem ..)
    | off => simp [Action.gate]
    | pair e => simp [Action.gate]
  · intro j hj i hi
    rw [len] at hj
    rw [compiledAt _ _ hj] at hi
    cases ha : A j with
    | keep => rw [ha] at hi; exact hb j hj i hi
    | off => simp [ha, Action.gate] at hi
    | pair e =>
      simp [ha, Action.gate] at hi
      have hp := e.1.isLt
      have hl := e.2.isLt
      rcases hi with rfl | rfl <;> omega

theorem input {N} (C : Circuit) (x : Bits N) (i : Fin (N+N)) : value C i x = x i := by
  unfold value
  rw [wires_input _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, i.isLt]

theorem evalAt {N} (C : Circuit) (x : Bits N) {j} (hj : j < C.gates.length) :
    value C (N+N+j) x = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < N+N+j then value C i x else false) := by
  simpa [value, rd, atGate _ hj] using wires_gate C (List.ofFn x) j hj

theorem outside {N} (C : Circuit) (x : Bits N) {w} (hw : N+N+C.gates.length ≤ w) :
    value C w x = false := by
  apply List.getD_eq_default
  simpa [wires_length] using hw

theorem evalPair {N} (A : ℕ → Action N) (C : Circuit) {j} (hj : j < C.gates.length)
    {e} (he : A j = .pair e) (x : Bits N) :
    value (compile A C) (N+N+j) x = (x (Fin.castAdd N e.1) && x (Fin.natAdd N e.2)) := by
  rw [evalAt _ _ (by simpa using hj), compiledAt _ _ hj, he]
  have hp : (Fin.castAdd N e.1).val < N+N+j := by have := (Fin.castAdd N e.1).isLt; omega
  have hl : (Fin.natAdd N e.2).val < N+N+j := by have := (Fin.natAdd N e.2).isLt; omega
  simp only [Action.gate, List.map_cons, List.map_nil, hp, hl, ↓reduceIte, input]
  simp [GateOp.eval]

theorem evalOff {N} (A : ℕ → Action N) (C : Circuit) {j} (hj : j < C.gates.length)
    (he : A j = .off) (x : Bits N) : value (compile A C) (N+N+j) x = false := by
  rw [evalAt _ _ (by simpa using hj), compiledAt _ _ hj, he]
  rfl

theorem wireMono {N} (C : Circuit) (hm : Monotone2 C) (x y : Bits N)
    (h : ∀ k, x k = true → y k = true) (w : ℕ) : value C w x = true → value C w y = true := by
  apply wires_mono C (fun g hg => (hm g hg).1) _ _ (by simp)
  intro i hi
  by_cases hh : i < N+N
  · simpa [List.getD_eq_getElem?_getD, hh] using
      h ⟨i,hh⟩ (by simpa [List.getD_eq_getElem?_getD, hh] using hi)
  · simp [List.getD_eq_getElem?_getD, hh] at hi

theorem rowBelow {N} (e : Pair N) (x : Bits N)
    (hp : x (Fin.castAdd N e.1) = true) (hl : x (Fin.natAdd N e.2) = true) :
    ∀ k, row e k = true → x k = true := by
  intro k h
  simp only [row, decide_eq_true_eq] at h
  rcases h with rfl | rfl <;> assumption

theorem rowHits {N} (a e : Pair N) :
    (row a (Fin.castAdd N e.1) && row a (Fin.natAdd N e.2)) = true ↔ a = e := by
  have cross (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
    intro h
    have hv := congrArg Fin.val h
    change p.val = N+l.val at hv
    have := p.isLt
    omega
  calc
    _ ↔ e = a := by
      simp only [row, Bool.and_eq_true, decide_eq_true_eq, cross, (cross a.1 e.2).symm,
        or_false, false_or, Fin.castAdd_inj, Prod.ext_iff]
      simp
    _ ↔ a = e := eq_comm

structure Certified {N} (I : Fin N → Fin N → Prop) (C : Circuit) (A : ℕ → Action N) : Prop where
  off : ∀ j, A j = .off → ∀ e, ¬ supported I C j e
  pair : ∀ j e, A j = .pair e → supported I C j e ∧ ∀ f, supported I C j f → f = e

theorem planCertified {N} (I : Fin N → Fin N → Prop) (C : Circuit) :
    Certified I C (plan I C) := by
  classical
  constructor
  · intro j hh
    unfold plan at hh
    split at hh <;> try contradiction
    split at hh
    · split at hh <;> contradiction
    · intro e he
      exact ‹¬ ∃ _, _› ⟨e, he⟩
  · intro j e hh
    unfold plan at hh
    split at hh <;> try contradiction
    split at hh <;> try contradiction
    split at hh <;> try contradiction
    cases hh
    rename_i hu
    exact hu.choose_spec

-- A common induction for forward domination and reverse domination on a flag.
theorem wireTransfer {N} (A : ℕ → Action N) (C : Circuit) (hm : Monotone2 C) (x : Bits N)
    (P Q : Circuit) (hP : P = C ∨ P = compile A C) (hQ : Q = C ∨ Q = compile A C)
    (replace : ∀ j < C.gates.length, A j ≠ .keep →
      value P (N+N+j) x = true → value Q (N+N+j) x = true)
    (w : ℕ) : value P w x = true → value Q w x = true := by
  have pLen : P.gates.length = C.gates.length := by rcases hP with rfl | rfl <;> simp
  have qLen : Q.gates.length = C.gates.length := by rcases hQ with rfl | rfl <;> simp
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hIn : w < N+N
    · simp only [input (i := ⟨w,hIn⟩), imp_self]
    by_cases hOut : N+N+C.gates.length ≤ w
    · rw [outside P x (by rwa [pLen])]
      simp
    let j := w - (N+N)
    have hj : j < C.gates.length := by dsimp [j]; omega
    have hw : w = N+N+j := by dsimp [j]; omega
    by_cases hk : A j = .keep
    · have pg : gateAt P j = gateAt C j := by rcases hP with rfl | rfl <;> simp [compiledAt, hj, hk, Action.gate]
      have qg : gateAt Q j = gateAt C j := by rcases hQ with rfl | rfl <;> simp [compiledAt, hj, hk, Action.gate]
      rw [hw, evalAt P x (by rwa [pLen]), evalAt Q x (by rwa [qLen]), pg, qg]
      apply eval_mono _ (by rw [atGate C hj]; exact (hm _ (List.getElem_mem ..)).1)
      intro k hk'
      by_cases smaller : k < N+N+j
      · simp only [smaller, ↓reduceIte] at hk' ⊢
        exact ih k (by omega) hk'
      · simp [smaller] at hk'
    · rw [hw]
      exact replace j hj hk

theorem below {N} (I : Fin N → Fin N → Prop) (C : Circuit) (hm : Monotone2 C)
    (A : ℕ → Action N) (cert : Certified I C A) (x : Bits N) (w : ℕ) :
    value (compile A C) w x = true → value C w x = true := by
  apply wireTransfer A C hm x _ _ (Or.inr rfl) (Or.inl rfl) _ w
  intro j hj hk h
  cases ha : A j with
  | keep => exact (hk ha).elim
  | off => simp [evalOff A C hj ha] at h
  | pair e =>
    rw [evalPair A C hj ha, Bool.and_eq_true] at h
    exact wireMono C hm _ x (rowBelow e x h.1 h.2) _ (cert.pair j e ha).1.2

theorem agree {N} (I : Fin N → Fin N → Prop) (C : Circuit) (hm : Monotone2 C)
    (A : ℕ → Action N) (cert : Certified I C A) (e : Pair N) (he : I e.1 e.2) (w : ℕ) :
    value (compile A C) w (row e) = value C w (row e) := by
  apply Bool.eq_iff_iff.mpr
  refine ⟨below I C hm A cert _ _, ?_⟩
  apply wireTransfer A C hm (row e) _ _ (Or.inl rfl) (Or.inr rfl) _ w
  intro j hj hk h
  cases ha : A j with
  | keep => exact (hk ha).elim
  | off => exact (cert.off j ha e ⟨he,h⟩).elim
  | pair f =>
    rw [evalPair A C hj ha, rowHits]
    exact (cert.pair j f ha).2 e ⟨he,h⟩

abbrev OutputSpec {N} (I : Fin N → Fin N → Prop) (C : Circuit) :=
  ∀ x : Bits N, circuitFun (N+N) C x = true ↔
    ∃ e : Pair N, I e.1 e.2 ∧ x (Fin.castAdd N e.1) = true ∧ x (Fin.natAdd N e.2) = true

theorem outputPreserved {N} (I : Fin N → Fin N → Prop) (C : Circuit)
    (hm : Monotone2 C) (hb : ReadsBack (N+N) C) (hc : OutputSpec I C)
    (A : ℕ → Action N) (cert : Certified I C A) : OutputSpec I (compile A C) := by
  intro x
  constructor
  · intro h
    exact (hc x).mp (below I C hm A cert x C.output h)
  · rintro ⟨e,he,hp,hl⟩
    have old : value C C.output (row e) = true := (hc (row e)).mpr
      ⟨e, he, by simp [row], by simp [row]⟩
    exact wireMono (compile A C) (shape A C hm hb).1 _ x (rowBelow e x hp hl) C.output
      (by rwa [agree I C hm A cert e he C.output])

abbrev one {N} (v : Fin (N+N)) : Bits N := fun i => decide (i = v)

abbrev NoSingleton {N : ℕ} (C : Circuit) :=
  ∀ j < C.gates.length, (gateAt C j).op = .and →
    ∀ v : Fin (N+N), value C (N+N+j) (one v) = false

theorem stillAnd {N} (I : Fin N → Fin N → Prop) (C : Circuit) {j}
    (hj : j < C.gates.length) (hg : (gateAt (compile (plan I C) C) j).op = .and) :
    (gateAt C j).op = .and := by
  by_contra h
  have hk : plan I C j = .keep := by simp [plan, h]
  simp [compiledAt, hj, hk, Action.gate, h] at hg

theorem singletonPreserved {N} (I : Fin N → Fin N → Prop) (C : Circuit) (hm : Monotone2 C)
    (hone : NoSingleton (N:=N) C) : NoSingleton (N:=N) (compile (plan I C) C) := by
  intro j hj hg v
  rw [len] at hj
  have hold := hone j hj (stillAnd I C hj hg) v
  have h := below I C hm (plan I C) (planCertified I C) (one v) (N+N+j)
  cases hh : value (compile (plan I C) C) (N+N+j) (one v) <;> simp_all

theorem keepTwo {N} (I : Fin N → Fin N → Prop) (C : Circuit) (j : ℕ)
    (hg : (gateAt C j).op = .and) (hk : plan I C j = .keep) :
    ∃ e f : Pair N, e ≠ f ∧ supported I C j e ∧ supported I C j f := by
  classical
  by_cases hex : ∃ e, supported I C j e
  · obtain ⟨e,he⟩ := hex
    by_contra! h
    have hu : ∃ e, supported I C j e ∧ ∀ f, supported I C j f → f = e := by
      refine ⟨e,he,?_⟩
      intro f hf
      by_contra hne
      exact h e f (Ne.symm hne) he hf
    have hex' : ∃ e, supported I C j e := ⟨e,he⟩
    simp only [plan, hg, hex', hu, ↓reduceIte, ↓reduceDIte] at hk
    cases hk
  · simp [plan, hg, hex] at hk

abbrev FiresOnNonedge {N} (I : Fin N → Fin N → Prop) (C : Circuit) (j : ℕ) :=
  ∃ a : Pair N, ¬I a.1 a.2 ∧ value C (N+N+j) (row a) = true

theorem remaining {N} (I : Fin N → Fin N → Prop) (C : Circuit) (hm : Monotone2 C)
    {j} (hj : j < C.gates.length) (hg : (gateAt (compile (plan I C) C) j).op = .and)
    (hd : FiresOnNonedge I (compile (plan I C) C) j) :
    ∃ e f : Pair N, e ≠ f ∧ supported I (compile (plan I C) C) j e ∧
      supported I (compile (plan I C) C) j f := by
  have cert := planCertified I C
  obtain ⟨a,ha,va⟩ := hd
  cases hk : plan I C j with
  | off => simp [evalOff _ C hj hk] at va
  | pair e =>
    have eq := (rowHits a e).mp (by rwa [evalPair _ C hj hk] at va)
    exact (ha (eq ▸ (cert.pair j e hk).1.1)).elim
  | keep =>
    obtain ⟨e,f,hef,he,hf⟩ := keepTwo I C j (stillAnd I C hj hg) hk
    exact ⟨e,f,hef,⟨he.1, (agree I C hm _ cert e he.1 _).trans he.2⟩,
      ⟨hf.1, (agree I C hm _ cert f hf.1 _).trans hf.2⟩⟩

/-- All flags and all outputs are preserved. Every remaining AND that fires on a
nonincident cross pair fires on at least two distinct genuine flags. -/
theorem prune {N} (I : Fin N → Fin N → Prop) (C : Circuit) (hm : Monotone2 C)
    (hb : ReadsBack (N+N) C) (hc : OutputSpec I C) (hone : NoSingleton (N:=N) C) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N+N) D ∧ D.size = C.size ∧ OutputSpec I D ∧
      NoSingleton (N:=N) D ∧
      (∀ e : Pair N, I e.1 e.2 → ∀ w, value D w (row e) = value C w (row e)) ∧
      ∀ j < D.gates.length, (gateAt D j).op = .and → FiresOnNonedge I D j →
        ∃ e f : Pair N, e ≠ f ∧ supported I D j e ∧ supported I D j f := by
  let A := plan I C
  have cert := planCertified I C
  exact ⟨compile A C,(shape A C hm hb).1,(shape A C hm hb).2,len,
    outputPreserved I C hm hb hc A cert,singletonPreserved I C hm hone,
    fun e he w => agree I C hm A cert e he w,
    fun _ hj hg hd => remaining I C hm (by simpa using hj) hg hd⟩

/-- The full cleaning conclusion for circuits whose AND gates accepting a
nonedge each accept at most one genuine edge. Other ANDs are unrestricted. -/
theorem exactIfSparse {N} (I : Fin N → Fin N → Prop) (C : Circuit) (hm : Monotone2 C)
    (hb : ReadsBack (N+N) C) (hc : OutputSpec I C) (hone : NoSingleton (N:=N) C)
    (sparse : ∀ j < C.gates.length, (gateAt C j).op = .and → FiresOnNonedge I C j →
      ∀ e f, supported I C j e → supported I C j f → e = f) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N+N) D ∧ D.size = C.size ∧ OutputSpec I D ∧
      NoSingleton (N:=N) D ∧ ∀ j < D.gates.length, (gateAt D j).op = .and →
        ¬FiresOnNonedge I D j := by
  let A := plan I C
  have cert := planCertified I C
  refine ⟨compile A C,(shape A C hm hb).1,(shape A C hm hb).2,len,
    outputPreserved I C hm hb hc A cert,singletonPreserved I C hm hone,?_⟩
  intro j hj hg hd
  rw [len] at hj
  obtain ⟨e,f,hef,he,hf⟩ := remaining I C hm hj hg hd
  obtain ⟨a,ha,va⟩ := hd
  exact hef (sparse j hj (stillAnd I C hj hg) ⟨a,ha,below I C hm A cert _ _ va⟩ e f
    ⟨he.1,below I C hm A cert _ _ he.2⟩ ⟨hf.1,below I C hm A cert _ _ hf.2⟩)

namespace MatchingExample

-- Input order is p0, p1, l0, l1. Wire 6 is the full two-by-two rectangle.
def seven : Circuit :=
  ⟨[⟨.or,[0,1]⟩, ⟨.or,[2,3]⟩, ⟨.and,[4,5]⟩, ⟨.or,[0,3]⟩, ⟨.and,[6,7]⟩,
    ⟨.or,[1,2]⟩, ⟨.and,[8,9]⟩],10⟩

def three : Circuit := ⟨[⟨.and,[0,2]⟩, ⟨.and,[1,3]⟩, ⟨.or,[4,5]⟩],6⟩
def diagonal (p l : Fin 2) : Prop := p = l
instance : DecidableRel diagonal := fun p l => inferInstanceAs (Decidable (p = l))

theorem smallExact : OutputSpec diagonal seven ∧ OutputSpec diagonal three := by
  unfold OutputSpec
  decide

theorem smallShapes : Monotone2 seven ∧ ReadsBack 4 seven ∧ NoSingleton (N:=2) seven := by
  refine ⟨?_,?_,?_⟩
  · intro g hg
    simp only [seven, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro j hj
    change j < 7 at hj
    interval_cases j <;> simp [gateAt, seven]
  · intro j hj
    change j < 7 at hj
    interval_cases j <;> intro hg <;> simp [seven, gateAt] at hg <;> decide

theorem rectangle : supported diagonal seven 2 (0,0) ∧ supported diagonal seven 2 (1,1) ∧
    value seven 6 (row (0,1) : Bits 2) = true ∧ value seven 6 (row (1,0) : Bits 2) = true := by
  unfold supported
  decide

def candidate (isAnd : Bool) (a b : Fin 6) (e : Pair 2) : Bool :=
  let u := value seven a (row e)
  let v := value seven b (row e)
  if isAnd then u && v else u || v

-- No AND or OR of two earlier wires keeps both matching edges and excludes
-- both off-diagonal pairs. Repeated operands cover unary replacements.
theorem noLocalReplacement : ∀ isAnd (a b : Fin 6),
    candidate isAnd a b (0,0) = true → candidate isAnd a b (1,1) = true →
    candidate isAnd a b (0,1) = true ∨ candidate isAnd a b (1,0) = true := by
  decide

theorem threeClean : Monotone2 three ∧ ReadsBack 4 three ∧ NoSingleton (N:=2) three ∧
    ∀ j < three.gates.length, (gateAt three j).op = .and → ¬FiresOnNonedge diagonal three j := by
  refine ⟨?_,?_,?_,?_⟩
  · intro g hg
    simp only [three, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> simp
  · intro j hj
    change j < 3 at hj
    interval_cases j <;> simp [gateAt, three]
  · intro j hj
    change j < 3 at hj
    interval_cases j <;> intro hg <;> simp [three, gateAt] at hg <;> decide
  · intro j hj
    change j < 3 at hj
    interval_cases j <;> intro hg <;> simp [three, gateAt] at hg <;> unfold FiresOnNonedge <;> decide

end MatchingExample
end FlagPruning
