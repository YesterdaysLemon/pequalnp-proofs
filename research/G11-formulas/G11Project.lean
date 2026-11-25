import G11Bridge
import PEqualNP.Defs.EdgeOwnership

namespace G11Game
open KWPartition PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

abbrev source := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
  (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]

set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
theorem graph_agrees : ∀ x : V → Bool, graph x = graphFun source ∅ x := by decide +kernel

theorem formula_size (proof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (checked : Std.Tactic.BVDecide.LRAT.check proof (KWEncoding.problem game 22) = true) (k : Nat) :
    (∃ f : Formula V, f.gates ≤ k ∧ ∀ x, f.eval x = graphFun source ∅ x) ↔ 22 ≤ k := by
  have h := exact_size (Std.Tactic.BVDecide.LRAT.check_sound proof _ checked) k
  simpa only [graph_agrees] using h

end G11Game
