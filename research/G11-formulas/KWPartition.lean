import Mathlib.Data.Finset.Card

namespace KWPartition

inductive Formula (V : Type) where
  | var (v : V)
  | meet (left right : Formula V)
  | join (left right : Formula V)

namespace Formula

def eval (x : V → Bool) : Formula V → Bool
  | .var v => x v
  | .meet l r => eval x l && eval x r
  | .join l r => eval x l || eval x r

def leaves : Formula V → Nat
  | .var _ => 1
  | .meet l r | .join l r => l.leaves+r.leaves

def gates : Formula V → Nat
  | .var _ => 0
  | .meet l r | .join l r => l.gates+r.gates+1

theorem leaf_count (f : Formula V) : f.leaves = f.gates+1 := by
  induction f <;> simp_all [leaves,gates] <;> omega

end Formula

structure Rect (R C V : Type) where
  label : V
  rows : Finset R
  cols : Finset C

variable {R C V : Type} [DecidableEq R] [DecidableEq C]
variable (yes : R → V → Bool) (no : C → V → Bool)

def tiles : Formula V → Finset R → Finset C → List (Rect R C V)
  | .var v,A,B => [⟨v,A,B⟩]
  | .join l r,A,B =>
    tiles l (A.filter (fun i => l.eval (yes i) = true)) B ++
    tiles r (A.filter (fun i => l.eval (yes i) = false)) B
  | .meet l r,A,B =>
    tiles l A (B.filter (fun j => l.eval (no j) = false)) ++
    tiles r A (B.filter (fun j => l.eval (no j) = true))

def hits (i : R) (j : C) (r : Rect R C V) : Bool := decide (i ∈ r.rows ∧ j ∈ r.cols)
def valid (r : Rect R C V) : Prop :=
  (∀ i ∈ r.rows, yes i r.label = true) ∧ (∀ j ∈ r.cols, no j r.label = false)

theorem size_tiles (f : Formula V) (A : Finset R) (B : Finset C) :
    (tiles yes no f A B).length = f.leaves := by
  induction f generalizing A B <;> simp_all [tiles,Formula.leaves]

theorem partition (f : Formula V) (A : Finset R) (B : Finset C) (i : R) (j : C) :
    (tiles yes no f A B).countP (hits i j) = if i ∈ A ∧ j ∈ B then 1 else 0 := by
  induction f generalizing A B with
  | var v => simp [tiles,hits]
  | join l r hl hr =>
    simp only [tiles,List.countP_append,hl,hr,Finset.mem_filter]
    cases e : l.eval (yes i) <;> simp [e,and_assoc]
  | meet l r hl hr =>
    simp only [tiles,List.countP_append,hl,hr,Finset.mem_filter]
    cases e : l.eval (no j) <;> simp [e,and_assoc]

theorem all_valid (f : Formula V) (A : Finset R) (B : Finset C)
    (pos : ∀ i ∈ A, f.eval (yes i) = true) (neg : ∀ j ∈ B, f.eval (no j) = false) :
    ∀ t ∈ tiles yes no f A B, valid yes no t := by
  induction f generalizing A B with
  | var v =>
    intro t ht
    obtain rfl := List.mem_singleton.mp ht
    exact ⟨pos,neg⟩
  | join l r hl hr =>
    intro t ht
    rcases List.mem_append.mp ht with left | right
    · apply hl _ _ (fun _ h => (Finset.mem_filter.mp h).2) _ _ left
      intro j hj
      exact (Bool.or_eq_false_iff.mp (neg j hj)).1
    · apply hr _ _ _ _ _ right
      · intro i hi
        obtain ⟨ha,zero⟩ := Finset.mem_filter.mp hi
        simpa [Formula.eval,zero] using pos i ha
      · intro j hj
        exact (Bool.or_eq_false_iff.mp (neg j hj)).2
  | meet l r hl hr =>
    intro t ht
    rcases List.mem_append.mp ht with left | right
    · apply hl _ _ _ (fun _ h => (Finset.mem_filter.mp h).2) _ left
      exact fun i hi => (Bool.and_eq_true_iff.mp (pos i hi)).1
    · apply hr _ _ _ _ _ right
      · exact fun i hi => (Bool.and_eq_true_iff.mp (pos i hi)).2
      · intro j hj
        obtain ⟨hb,one⟩ := Finset.mem_filter.mp hj
        simpa [Formula.eval,one] using neg j hb

end KWPartition
