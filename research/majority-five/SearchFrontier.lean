import FullProjection

namespace FullSearch
abbrev Node := Nat × List W

def enqueue (yes : Bool) (node : Node) : List Node := if yes then [node] else []

theorem enqueue_any (yes : Bool) (n : Node) (p : Node → Bool) :
    (enqueue yes n).any p = (yes && p n) := by cases yes <;> simp [enqueue]

def afterGate (e : Nat) (a b : W) (r : List W) : List Node :=
  (ops a b).flatMap fun w =>
    let v := sep w ||| cuts r
    enqueue (v == -1) (e,w :: r) ++
    enqueue ((e != 0) && (v ||| sep a == -1)) (e-1,w :: a :: r) ++
    enqueue ((e != 0) && (v ||| sep b == -1)) (e-1,w :: b :: r) ++
    enqueue (decide (e ≥ 2) && (v ||| sep a ||| sep b == -1)) (e-2,w :: a :: b :: r)

theorem dispatch_nodes (e : Nat) (next : Nat → List W → Bool) (a b : W) (r : List W) :
    dispatch e next a b r = (afterGate e a b r).any (fun n => next n.1 n.2) := by
  unfold dispatch afterGate
  rw [List.any_flatMap]
  apply congrArg (List.any (ops a b))
  funext w
  simp only [List.any_append,enqueue_any,Bool.and_or_distrib_left,Bool.and_assoc,Bool.or_assoc]

def nodes (e : Nat) (ws : List W) : List Node :=
  (pairs ws).flatMap fun (a,b,r) => afterGate e a b r

theorem next_false {ws : List W} {k e : Nat}
    (start : (ws == [goal] || ws == [~~~goal]) = false)
    (children : ∀ n ∈ nodes e ws, optimized k n.1 n.2 = false) :
    optimized (k+1) e ws = false := by
  have no : (nodes e ws).any (fun n => optimized k n.1 n.2) = false := by
    apply Bool.eq_false_iff.mpr
    intro yes
    obtain ⟨n,hn,ok⟩ := List.any_eq_true.mp yes
    rw [children n hn] at ok
    contradiction
  rw [nodes,List.any_flatMap] at no
  rw [optimized,start,Bool.false_or]
  simpa only [dispatch_nodes] using no

theorem closed_from_root {inputs : List W} {k : Nat}
    (onlyRoot : inputs.sublists.all (fun ws => (cuts ws != -1) || (ws == inputs)) = true)
    (closed : optimized k (k+1-inputs.length) inputs = false) : search k inputs = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨ws,mem,ok⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  have test := List.all_eq_true.mp onlyRoot ws mem
  have good : cuts ws = -1 := ok.1.2
  have same : ws = inputs := by simpa [good] using test
  rw [same,closed] at ok
  simp at ok

end FullSearch
