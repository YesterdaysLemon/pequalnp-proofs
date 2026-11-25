import PairedCircuit
import PEqualNP.Defs.MetaComplexityLgpMono

namespace Paired
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

inductive Formula where
  | var (p : Coord)
  | gate (isAnd : Bool) (l r : Formula)

namespace Formula

def size : Formula → ℕ
  | .var _ => 0
  | .gate _ l r => l.size + r.size + 1

def eval (x : Row) : Formula → Bool
  | .var p => x p
  | .gate isAnd l r => if isAnd then l.eval x && r.eval x else l.eval x || r.eval x

def fits (ks : List Coord) : Formula → Prop
  | .var p => p ∈ ks
  | .gate _ l r => l.fits ks ∧ r.fits ks

def output (ks : List Coord) (start : ℕ) : Formula → ℕ
  | .var p => ks.idxOf p
  | .gate _ l r => start + l.size + r.size

def emit (ks : List Coord) (start : ℕ) : Formula → List Gate
  | .var _ => []
  | .gate isAnd l r =>
    l.emit ks start ++ r.emit ks (start + l.size) ++
      [⟨if isAnd then .and else .or, [l.output ks start,r.output ks (start + l.size)]⟩]

theorem length_emit (e : Formula) (ks : List Coord) (start : ℕ) :
    (e.emit ks start).length = e.size := by
  induction e generalizing start with
  | var => rfl
  | gate b l r ih₁ ih₂ => simp [emit,size,ih₁,ih₂,Nat.add_assoc]

theorem monotone_emit (e : Formula) (ks : List Coord) (start : ℕ) :
    ∀ g ∈ e.emit ks start, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  induction e generalizing start with
  | var p => simp [emit]
  | gate b l r ih₁ ih₂ =>
    intro g hg
    simp only [emit,List.mem_append,List.mem_singleton] at hg
    rcases hg with (left | right) | rfl
    · exact ih₁ _ _ left
    · exact ih₂ _ _ right
    · cases b <;> simp

def applyGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def run (gs : List Gate) (w : List Bool) := gs.foldl applyGate w

theorem run_extends (gs : List Gate) (w : List Bool) :
    ∃ t, run gs w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[],by simp [run],rfl⟩
  | cons g gs ih =>
    obtain ⟨t,e,len⟩ := ih (applyGate w g)
    exact ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t,
      by simpa [run,applyGate] using e, by simp [len]⟩

theorem run_length (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  obtain ⟨t,e,len⟩ := run_extends gs w
  simp [e,len]

theorem run_read (gs : List Gate) (w : List Bool) {i : ℕ} (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  obtain ⟨t,e,_⟩ := run_extends gs w
  exact e ▸ List.getD_append _ _ _ _ hi

theorem emit_sound (e : Formula) (ks : List Coord) (x : Row) (ok : e.fits ks)
    (w : List Bool)
    (avail : ∀ p ∈ ks, ks.idxOf p < w.length ∧ w.getD (ks.idxOf p) false = x p) :
    let v := run (e.emit ks w.length) w
    e.output ks w.length < v.length ∧ v.getD (e.output ks w.length) false = e.eval x := by
  induction e generalizing w with
  | var p => exact avail p ok
  | gate b l r ih₁ ih₂ =>
    let wl := run (l.emit ks w.length) w
    have lenl : wl.length = w.length + l.size := (run_length ..).trans (by rw [length_emit])
    obtain ⟨hl,el⟩ := ih₁ ok.1 w avail
    have more : ∀ p ∈ ks, ks.idxOf p < wl.length ∧ wl.getD (ks.idxOf p) false = x p := by
      intro p hp
      obtain ⟨bd,eq⟩ := avail p hp
      exact ⟨by omega,(run_read _ w bd).trans eq⟩
    obtain ⟨hr,er⟩ := ih₂ ok.2 wl more
    let wr := run (r.emit ks wl.length) wl
    have lenr : wr.length = w.length + l.size + r.size := by
      simp [wr,run_length,length_emit,lenl]
    have left : wr.getD (l.output ks w.length) false = l.eval x := (run_read _ wl hl).trans el
    have right : wr.getD (r.output ks wl.length) false = r.eval x := er
    let op : GateOp := if b then .and else .or
    let g : Gate := ⟨op,[l.output ks w.length,r.output ks wl.length]⟩
    have eq : run ((Formula.gate b l r).emit ks w.length) w = applyGate wr g := by
      simp only [emit,run,List.foldl_append,List.foldl_cons,List.foldl_nil]
      dsimp [wr,g,op,run]
      rw [lenl]
      rfl
    dsimp only
    rw [eq]
    have pos : (Formula.gate b l r).output ks w.length = wr.length := lenr.symm
    rw [pos]
    constructor
    · simp [applyGate]
    · simp only [applyGate,List.getD_eq_getElem?_getD,List.getElem?_append_right (Nat.le_refl _),
        Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]
      change op.eval [wr.getD (l.output ks w.length) false,wr.getD (r.output ks wl.length) false] =
        (Formula.gate b l r).eval x
      rw [left,right]
      cases b <;> simp [op,eval,GateOp.eval]

def circuit (e : Formula) (ks : List Coord) : Circuit := ⟨e.emit ks ks.length,e.output ks ks.length⟩

theorem circuit_correct (e : Formula) (ks : List Coord) (x : Row) (ok : e.fits ks) :
    (e.circuit ks).eval (ks.map x) = e.eval x := by
  have known (p : Coord) (hp : p ∈ ks) :
      ks.idxOf p < (ks.map x).length ∧ (ks.map x).getD (ks.idxOf p) false = x p := by
    have bd := List.idxOf_lt_length_of_mem hp
    refine ⟨by simpa using bd,?_⟩
    rw [List.getD_eq_getElem _ _ (by simpa using bd),List.getElem_map,List.getElem_idxOf]
  have sound := (emit_sound e ks x ok (ks.map x) known).2
  simp only [List.length_map] at sound
  exact sound

end Formula

def allFirst : ℕ → Formula
  | 0 => .var (0,false)
  | m+1 => .gate true (allFirst m) (.var (m+1,false))

def joinProducts : ℕ → Formula → Formula
  | 0, e => e
  | k+1, e => .gate false (joinProducts k e) (.gate true (.var (k,false)) (.var (k,true)))

-- For m + 2 indices, the last a input factors out of the long conjunction.
def expression (m : ℕ) : Formula :=
  joinProducts (m+1) (.gate true (.var (m+1,false)) (.gate false (.var (m+1,true)) (allFirst m)))

theorem allFirst_size (m : ℕ) : (allFirst m).size = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [allFirst,Formula.size,ih]

theorem joinProducts_size (k : ℕ) (e : Formula) : (joinProducts k e).size = 2*k+e.size := by
  induction k with
  | zero => simp [joinProducts]
  | succ k ih => simp [joinProducts,Formula.size,ih]; omega

theorem expression_size (m : ℕ) : (expression m).size = 3*m+4 := by
  simp [expression,joinProducts_size,Formula.size,allFirst_size]
  omega

theorem allFirst_fits {m n : ℕ} (h : m < n) : (allFirst m).fits (labels n) := by
  induction m with
  | zero => exact (label_mem n _).mpr h
  | succ m ih => exact ⟨ih (by omega),(label_mem n _).mpr h⟩

theorem joinProducts_fits {k n : ℕ} (h : k ≤ n) (e : Formula) (he : e.fits (labels n)) :
    (joinProducts k e).fits (labels n) := by
  induction k with
  | zero => exact he
  | succ k ih => exact ⟨ih (by omega),(label_mem n _).mpr (by omega),(label_mem n _).mpr (by omega)⟩

theorem expression_fits (m : ℕ) : (expression m).fits (labels (m+2)) :=
  joinProducts_fits (by omega) _ ⟨(label_mem _ _).mpr (by omega),
    (label_mem _ _).mpr (by omega),allFirst_fits (by omega)⟩

theorem allFirst_true (m : ℕ) (x : Row) :
    (allFirst m).eval x = true ↔ ∀ i < m+1, x (i,false) = true := by
  induction m with
  | zero => simp [allFirst,Formula.eval]
  | succ m ih => simp only [allFirst,Formula.eval,ite_true,Bool.and_eq_true,ih,Nat.forall_lt_succ_right]

theorem joinProducts_true (k : ℕ) (e : Formula) (x : Row) :
    (joinProducts k e).eval x = true ↔ e.eval x = true ∨
      (∃ i < k, x (i,false) = true ∧ x (i,true) = true) := by
  induction k with
  | zero => simp [joinProducts]
  | succ k ih =>
    rw [show (∃ i < k+1, x (i,false) = true ∧ x (i,true) = true) ↔
      (∃ i < k, x (i,false) = true ∧ x (i,true) = true) ∨ x (k,false) = true ∧ x (k,true) = true
      from Nat.exists_lt_succ_right]
    simp [joinProducts,Formula.eval,ih,or_assoc]

theorem expression_correct (m : ℕ) (x : Row) :
    (expression m).eval x = value (Finset.range (m+2)) x := by
  apply Bool.eq_iff_iff.mpr
  change (_ = true) ↔ decide _ = true
  rw [decide_eq_true_iff]
  simp only [expression,joinProducts_true,Formula.eval,Bool.false_eq_true,ite_true,ite_false,Bool.and_eq_true,
    Bool.or_eq_true,allFirst_true,Finset.mem_range]
  have alln : (∀ i < m+2, x (i,false) = true) ↔
      (∀ i < m+1, x (i,false) = true) ∧ x (m+1,false) = true := Nat.forall_lt_succ_right
  have anyn : (∃ i < m+2, x (i,false) = true ∧ x (i,true) = true) ↔
      (∃ i < m+1, x (i,false) = true ∧ x (i,true) = true) ∨
        x (m+1,false) = true ∧ x (m+1,true) = true := Nat.exists_lt_succ_right
  rw [alln,anyn]
  have distribute (a b c d : Prop) : (a ∧ (b ∨ c) ∨ d) ↔ (c ∧ a ∨ d ∨ a ∧ b) := by tauto
  exact distribute _ _ _ _

theorem monotone_upper (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : Circuit, Monotone2 C ∧ C.size + 2 = 3*n ∧
      ∀ x : Row, C.eval ((labels n).map x) = value (Finset.range n) x := by
  obtain ⟨m,rfl⟩ : ∃ m, n = m+2 := ⟨n-2,by omega⟩
  refine ⟨(expression m).circuit (labels (m+2)),?_,?_,?_⟩
  · exact fun g hg => Formula.monotone_emit _ _ _ g hg
  · change ((expression m).emit _ _).length + 2 = _
    rw [Formula.length_emit,expression_size]
    omega
  · intro x
    exact ((expression m).circuit_correct _ x (expression_fits m)).trans (expression_correct m x)

end Paired
