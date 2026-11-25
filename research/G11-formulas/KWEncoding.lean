import Mathlib.Data.Nat.Pairing
import Std.Sat.CNF.Dimacs
import Std.Sat.CNF.Relabel
import Std.Tactic.BVDecide.LRAT

namespace KWEncoding
open Std.Sat

inductive Var where
  | select (p : Nat)
  | use (p j : Nat)
  | count (i t : Nat)
  deriving DecidableEq, Repr

def code : Var → Nat
  | .select p => 3*p
  | .use p j => 3*Nat.pair p j+1
  | .count i t => 3*Nat.pair i t+2

theorem code_injective : Function.Injective code := by
  intro x y eq
  cases x <;> cases y <;> simp only [code] at eq
  all_goals first | congr 1 <;> omega | omega | skip
  all_goals
    rename_i a b c d
    have h : Nat.pair a b = Nat.pair c d := by omega
    obtain ⟨rfl,rfl⟩ := Nat.pair_eq_pair.mp h
    rfl

abbrev Raw := List (Literal Var)
def pos (v : Var) : Literal Var := (v,true)
def neg (v : Var) : Literal Var := (v,false)

structure Game where
  patterns : Nat
  rows : Nat
  cols : Nat
  row : Nat → Nat → Bool
  col : Nat → Nat → Bool

def options (g : Game) (i j : Nat) : List Nat :=
  (List.range g.patterns).filter fun p => g.row p i && g.col p j

def cell (g : Game) (i j : Nat) : List Raw :=
  let ps := options g i j
  (ps.map (fun p => pos (.use p j))) ::
    ps.flatMap fun a => (ps.filter (fun b => decide (a<b))).map fun b => [neg (.use a j),neg (.use b j)]

def access (g : Game) : List Raw :=
  (List.range g.patterns).flatMap fun p =>
    ((List.range g.cols).filter (g.col p)).map fun j => [neg (.use p j),pos (.select p)]

def counterStep (b i : Nat) : List Raw :=
  [[neg (.select i),pos (.count (i+1) 1)]] ++
  ((List.range (b+1)).map fun t => [neg (.count i (t+1)),pos (.count (i+1) (t+1))]) ++
  ((List.range b).map fun t => [neg (.select i),neg (.count i (t+1)),pos (.count (i+1) (t+2))])

def cardinal (n b : Nat) : List Raw :=
  ((List.range (b+1)).map fun t => [neg (.count 0 (t+1))]) ++
  ((List.range n).flatMap (counterStep b)) ++ [[neg (.count n (b+1))]]

def raw (g : Game) (b : Nat) : List Raw :=
  access g ++ ((List.range g.rows).flatMap fun i => (List.range g.cols).flatMap fun j => cell g i j) ++
  cardinal g.patterns b

def named (g : Game) (b : Nat) : CNF Var := ⟨((raw g b).map CNF.Clause.ofLiterals).toArray⟩
def problem (g : Game) (b : Nat) : CNF Nat := (named g b).relabel code

def writeProblem (g : Game) (b : Nat) (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path (problem g b).dimacs

def verify (g : Game) (b : Nat) (path : System.FilePath) : IO Unit := do
  let proof ← Std.Tactic.BVDecide.LRAT.loadLRATProof path
  unless Std.Tactic.BVDecide.LRAT.check proof (problem g b) do
    throw (IO.userError "LRAT certificate failed")
  IO.println s!"Verified {proof.size} LRAT actions for the {b}-rectangle exclusion."

end KWEncoding
