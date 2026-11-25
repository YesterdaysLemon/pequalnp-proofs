import Std.Tactic.BVDecide.LRAT
import Std.Sat.CNF.Dimacs

open Std.Sat Std.Tactic.BVDecide

def loadDimacs (path : System.FilePath) : IO (CNF Nat) := do
  let input ← IO.FS.readFile path
  let mut vars := 0
  let mut declared : Option Nat := none
  let mut clauses := #[]
  for line in input.splitOn "\n" do
    let words := ((line.trimAscii.toString).splitOn " ").filter (· != "")
    match words with
    | [] | "c" :: _ => pure ()
    | ["p","cnf",v,c] =>
      if declared.isSome then throw (IO.userError "Duplicate problem line")
      let some n := v.toNat? | throw (IO.userError "Invalid variable count")
      let some m := c.toNat? | throw (IO.userError "Invalid clause count")
      vars := n
      declared := some m
    | ws =>
      if declared.isNone || ws.getLast? != some "0" then throw (IO.userError "Malformed clause")
      let mut literals := #[]
      for token in ws.dropLast do
        let some lit := token.toInt? | throw (IO.userError "Invalid literal")
        if lit == 0 || lit.natAbs > vars then throw (IO.userError "Variable outside DIMACS range")
        literals := literals.push (lit.natAbs-1,decide (0 < lit))
      clauses := clauses.push (CNF.Clause.ofLiterals literals.toList)
  if declared != some clauses.size then throw (IO.userError "Clause count does not match the header")
  return ⟨clauses⟩

def main (args : List String) : IO Unit := do
  let [problem,certificate] := args | throw (IO.userError "Pass the DIMACS problem and LRAT proof")
  let formula ← loadDimacs problem
  let actions ← LRAT.loadLRATProof certificate
  unless LRAT.check actions formula do throw (IO.userError "Certificate rejected")
  IO.println s!"Checked {actions.size} LRAT actions."
