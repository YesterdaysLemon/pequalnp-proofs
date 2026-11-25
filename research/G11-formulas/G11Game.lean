import KWEncoding

namespace G11Game
def edges : Array Nat := #[513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768]
def columns : Array Nat := #[15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,596,1066,1186,1288,1408,1546]
def keys : Array (Nat × Nat) := #[(0,1),(0,2),(0,3),(1,4),(1,8),(1,12),(2,16),(2,32),(2,48),(3,64),(3,128),(3,192),(4,4),(4,256),(4,512),(4,260),(4,516),(4,768),(4,772),(5,16),(5,1024),(5,2048),(5,1040),(5,2064),(5,3072),(5,3088),(6,64),(6,4096),(6,8192),(6,4160),(6,8256),(6,12288),(6,12352),(7,128),(7,4096),(7,16384),(7,4224),(7,16512),(7,20480),(7,20608),(8,8),(8,256),(8,1024),(8,32768),(8,264),(8,1032),(8,32776),(8,1280),(8,33024),(8,33792),(8,1288),(8,33032),(8,33800),(8,34048),(8,34056),(9,1),(9,2048),(9,16384),(9,32768),(9,2049),(9,16385),(9,32769),(9,18432),(9,34816),(9,49152),(9,18433),(9,34817),(9,49153),(9,51200),(9,51201),(10,2),(10,32),(10,512),(10,8192),(10,34),(10,514),(10,8194),(10,544),(10,8224),(10,8704),(10,546),(10,8226),(10,8706),(10,8736),(10,8738)]
def yes (r : Fin 16) (v : Fin 11) := (edges[r.val]?.getD 0).testBit v.val
def no (j : Fin 24) (v : Fin 11) := (columns[j.val]?.getD 0).testBit v.val
def label (p : Nat) := (keys[p]?.getD (0,0)).1
def members (p : Nat) := (keys[p]?.getD (0,0)).2
def game : KWEncoding.Game := ⟨85,16,24,fun p i => (members p).testBit i,
  fun p j => !((columns[j]?.getD 0).testBit (label p))⟩

def graph (x : Fin 11 → Bool) := (List.finRange 16).any fun r =>
  (List.finRange 11).all fun i => !(yes r i) || x i

theorem rows_positive : ∀ r, graph (yes r) = true := by decide +kernel
theorem cols_negative : ∀ j, graph (no j) = false := by decide +kernel
end G11Game

def main (args : List String) : IO Unit := do
  match args with
  | ["write",path] => KWEncoding.writeProblem G11Game.game 22 path
  | ["check",path] => KWEncoding.verify G11Game.game 22 path
  | _ => throw (IO.userError "Use write <cnf> or check <lrat>")
