import PEqualNP.Defs

namespace TreeResolution
open PEqualNP.ProofComplexity

abbrev V := Fin 5 × Fin 4
def bit (v : V) (x : ℕ) : Bool := x.testBit (4*v.1.val+v.2.val)
def row (p : Fin 5) : Clause V := Finset.univ.image (fun h : Fin 4 => ((p,h),true))
def collision (p q : Fin 5) (h : Fin 4) : Clause V := {((p,h),false),((q,h),false)}

def axiomList : List (Clause V) := [
  row 0,
  row 1,
  row 2,
  row 3,
  row 4,
  collision 0 1 0,
  collision 0 1 1,
  collision 0 1 2,
  collision 0 1 3,
  collision 0 2 0,
  collision 0 2 1,
  collision 0 2 2,
  collision 0 2 3,
  collision 0 3 0,
  collision 0 3 1,
  collision 0 3 2,
  collision 0 3 3,
  collision 0 4 0,
  collision 0 4 1,
  collision 0 4 2,
  collision 0 4 3,
  collision 1 2 0,
  collision 1 2 1,
  collision 1 2 2,
  collision 1 2 3,
  collision 1 3 0,
  collision 1 3 1,
  collision 1 3 2,
  collision 1 3 3,
  collision 1 4 0,
  collision 1 4 1,
  collision 1 4 2,
  collision 1 4 3,
  collision 2 3 0,
  collision 2 3 1,
  collision 2 3 2,
  collision 2 3 3,
  collision 2 4 0,
  collision 2 4 1,
  collision 2 4 2,
  collision 2 4 3,
  collision 3 4 0,
  collision 3 4 1,
  collision 3 4 2,
  collision 3 4 3]

def samples : List (List ℕ) := [
  [541200,295440,533520,164880,272400,149520,540960,295200,529440,99360,268320,84000,532800,164160,528960,98880,137280,75840,270720,147840,266880,82560,136320,74880],
  [541185,295425,533505,164865,272385,149505,540930,295170,529410,99330,268290,83970,532740,164100,528900,98820,137220,75780,270600,147720,266760,82440,136200,74760],
  [540705,294945,532545,163905,270465,147585,540690,294930,528450,98370,266370,82050,532500,163860,528420,98340,135300,73860,270360,147480,266280,81960,135240,73800],
  [525345,264225,524865,133185,262785,132225,525330,264210,524610,67650,262530,66690,524820,133140,524580,67620,131460,66180,262680,132120,262440,66600,131400,66120],
  [33825,18465,33345,10305,17025,9345,33810,18450,33090,6210,16770,5250,33300,10260,33060,6180,8580,4740,16920,9240,16680,5160,8520,4680],
  [541201,295441,533521,164881,272401,149521],
  [540962,295202,529442,99362,268322,84002],
  [532804,164164,528964,98884,137284,75844],
  [270728,147848,266888,82568,136328,74888],
  [540961,295201,532801,164161,270721,147841],
  [541202,295442,528962,98882,266882,82562],
  [533524,164884,529444,99364,136324,74884],
  [272408,149528,268328,84008,137288,75848],
  [529441,268321,528961,137281,266881,136321],
  [533522,272402,532802,75842,270722,74882],
  [541204,149524,540964,84004,147844,82564],
  [295448,164888,295208,99368,164168,98888],
  [99361,84001,98881,75841,82561,74881],
  [164882,149522,164162,137282,147842,136322],
  [295444,272404,295204,268324,270724,266884],
  [541208,533528,540968,529448,532808,528968],
  [540946,295186,532756,164116,270616,147736],
  [541217,295457,528932,98852,266792,82472],
  [533569,164929,529474,99394,136264,74824],
  [272513,149633,268418,84098,137348,75908],
  [529426,268306,528916,137236,266776,136216],
  [533537,272417,532772,75812,270632,74792],
  [541249,149569,540994,84034,147784,82504],
  [295553,164993,295298,99458,164228,98948],
  [99346,83986,98836,75796,82456,74776],
  [164897,149537,164132,137252,147752,136232],
  [295489,272449,295234,268354,270664,266824],
  [541313,533633,541058,529538,532868,529028],
  [528706,266626,528676,135556,266536,135496],
  [533057,270977,533012,74372,270872,74312],
  [541729,148609,541714,83074,148504,82984],
  [296993,165953,296978,100418,165908,100388],
  [98626,82306,98596,74116,82216,74056],
  [164417,148097,164372,135812,147992,135752],
  [295969,271489,295954,267394,271384,267304],
  [542753,534593,542738,530498,534548,530468],
  [71746,70786,71716,70276,70696,70216],
  [141377,140417,141332,139652,140312,139592],
  [280609,279169,280594,278914,279064,278824],
  [558113,557633,558098,557378,557588,557348]]

def axiomAt (k : Fin 45) : Clause V := axiomList[k.val]'(by exact k.isLt)
def sample (k : Fin 45) : List ℕ := samples[k.val]'(by exact k.isLt)

theorem complete : ∀ C ∈ PHP 5 4, ∃ k, axiomAt k = C := by
  rintro C (⟨p,rfl⟩ | ⟨p,q,h,hpq,rfl⟩)
  · exact (by decide : ∀ i : Fin 5, ∃ k, axiomAt k = row i) p
  · exact (by decide : ∀ i j : Fin 5, ∀ h : Fin 4, i ≠ j → ∃ k, axiomAt k = collision i j h) p q h hpq

def literalList : List (List (Literal V)) := [
  [((0,0),true),((0,1),true),((0,2),true),((0,3),true)],
  [((1,0),true),((1,1),true),((1,2),true),((1,3),true)],
  [((2,0),true),((2,1),true),((2,2),true),((2,3),true)],
  [((3,0),true),((3,1),true),((3,2),true),((3,3),true)],
  [((4,0),true),((4,1),true),((4,2),true),((4,3),true)],
  [((0,0),false),((1,0),false)],
  [((0,1),false),((1,1),false)],
  [((0,2),false),((1,2),false)],
  [((0,3),false),((1,3),false)],
  [((0,0),false),((2,0),false)],
  [((0,1),false),((2,1),false)],
  [((0,2),false),((2,2),false)],
  [((0,3),false),((2,3),false)],
  [((0,0),false),((3,0),false)],
  [((0,1),false),((3,1),false)],
  [((0,2),false),((3,2),false)],
  [((0,3),false),((3,3),false)],
  [((0,0),false),((4,0),false)],
  [((0,1),false),((4,1),false)],
  [((0,2),false),((4,2),false)],
  [((0,3),false),((4,3),false)],
  [((1,0),false),((2,0),false)],
  [((1,1),false),((2,1),false)],
  [((1,2),false),((2,2),false)],
  [((1,3),false),((2,3),false)],
  [((1,0),false),((3,0),false)],
  [((1,1),false),((3,1),false)],
  [((1,2),false),((3,2),false)],
  [((1,3),false),((3,3),false)],
  [((1,0),false),((4,0),false)],
  [((1,1),false),((4,1),false)],
  [((1,2),false),((4,2),false)],
  [((1,3),false),((4,3),false)],
  [((2,0),false),((3,0),false)],
  [((2,1),false),((3,1),false)],
  [((2,2),false),((3,2),false)],
  [((2,3),false),((3,3),false)],
  [((2,0),false),((4,0),false)],
  [((2,1),false),((4,1),false)],
  [((2,2),false),((4,2),false)],
  [((2,3),false),((4,3),false)],
  [((3,0),false),((4,0),false)],
  [((3,1),false),((4,1),false)],
  [((3,2),false),((4,2),false)],
  [((3,3),false),((4,3),false)]]
def axLits (k : Fin 45) : List (Literal V) := literalList[k.val]'(by exact k.isLt)
theorem litsCheck : ∀ k : Fin 45, (axLits k).toFinset = axiomAt k := by decide
def isFalse (x : ℕ) (k : Fin 45) : Bool := (axLits k).all fun lit => decide (bit lit.1 x ≠ lit.2)

theorem falseIff (x : ℕ) (k : Fin 45) :
    isFalse x k = true ↔ ¬ClauseSat (fun v => bit v x) (axiomAt k) := by
  rw [isFalse,List.all_eq_true,← litsCheck]
  constructor
  · rintro h ⟨q,hq,e⟩
    exact (of_decide_eq_true (h q (List.mem_toFinset.mp hq))) e
  · intro h q hq
    exact decide_eq_true (fun e => h ⟨q,List.mem_toFinset.mpr hq,e⟩)

set_option maxHeartbeats 5000000 in
theorem uniqueFalse : ∀ k : Fin 45, (sample k).all (fun x =>
    (List.finRange 45).all fun j => isFalse x j == decide (k=j)) = true := by
  intro k
  fin_cases k <;> decide +kernel

def labels (pred : ℕ → Bool) : Finset (Fin 45) :=
  Finset.univ.filter fun k => (sample k).any pred
def high (v : V) (x : ℕ) : Bool := bit v x
def low (v : V) (x : ℕ) : Bool := !(bit v x)
def both (P Q : ℕ → Bool) (x : ℕ) : Bool := P x && Q x

set_option maxHeartbeats 1500000 in
theorem highCount : ∀ v : V, 26 ≤ (labels (high v)).card := by decide +kernel
set_option maxHeartbeats 1500000 in
theorem lowCount : ∀ v : V, 41 ≤ (labels (low v)).card := by decide +kernel
set_option maxHeartbeats 12000000 in
theorem splitCount : ∀ v w : V, v ≠ w → 60 ≤
    (labels (both (low v) (low w))).card + (labels (both (low v) (high w))).card := by decide +kernel

inductive Tree
  | leaf (k : Fin 45)
  | query (v : V) (zero one : Tree)

def Tree.run : Tree → ℕ → Fin 45
  | .leaf k, _ => k
  | .query v zero one, x => if bit v x then one.run x else zero.run x
def Tree.leaves : Tree → ℕ
  | .leaf _ => 1
  | .query _ zero one => zero.leaves + one.leaves
def Tree.branches : Tree → ℕ
  | .leaf _ => 0
  | .query _ zero one => zero.branches + one.branches + 1
def Tree.names : Tree → Finset (Fin 45)
  | .leaf k => {k}
  | .query _ zero one => zero.names ∪ one.names

theorem branches_leaves (t : Tree) : t.branches + 1 = t.leaves := by
  induction t with
  | leaf => rfl
  | query _ _ _ hz ho => simp only [Tree.branches,Tree.leaves]; omega

theorem card_names (t : Tree) : t.names.card ≤ t.leaves := by
  induction t with
  | leaf => simp [Tree.names,Tree.leaves]
  | query _ _ _ hz ho =>
    exact (Finset.card_union_le ..).trans (Nat.add_le_add hz ho)

theorem mem_names (t : Tree) (x : ℕ) : t.run x ∈ t.names := by
  induction t with
  | leaf => simp [Tree.run,Tree.names]
  | query v z o hz ho =>
    cases h : bit v x <;> simp [Tree.run,Tree.names,h,hz,ho]

def Agrees (t : Tree) (P : ℕ → Bool) := ∀ k, ∀ x ∈ sample k, P x = true → t.run x = k

theorem count (t : Tree) (P : ℕ → Bool) (h : Agrees t P) : (labels P).card ≤ t.leaves := by
  apply le_trans (Finset.card_le_card (t := t.names) ?_) (card_names _)
  intro k hk
  obtain ⟨_,hh⟩ := Finset.mem_filter.mp hk
  obtain ⟨x,hx,hit⟩ := List.any_eq_true.mp hh
  exact h k x hx hit ▸ mem_names t x

theorem restrictLow {v z o P} (h : Agrees (.query v z o) P) : Agrees z (both P (low v)) := by
  intro k x hx hit
  simp only [both,Bool.and_eq_true] at hit
  obtain ⟨hP,hv⟩ := hit
  have hn : bit v x = false := by simpa [low] using hv
  simpa [Tree.run,hn] using h k x hx hP

theorem restrictHigh {v z o P} (h : Agrees (.query v z o) P) : Agrees o (both P (high v)) := by
  intro k x hx hit
  simp only [both,Bool.and_eq_true] at hit
  obtain ⟨hP,hv⟩ := hit
  change bit v x = true at hv
  simpa [Tree.run,hv] using h k x hx hP

theorem lowBranch (t : Tree) (v : V) (ok : Agrees t (low v)) : 60 ≤ t.leaves := by
  induction t with
  | leaf k =>
    have h := (lowCount v).trans (count (.leaf k) (low v) ok)
    simp [Tree.leaves] at h
  | query w z o ihz iho =>
    by_cases e : v = w
    · subst w
      have h := ihz (by
        intro k x hx hit
        exact restrictLow ok k x hx (by simp [both,hit]))
      exact h.trans (Nat.le_add_right ..)
    · exact (splitCount v w e).trans
        (Nat.add_le_add (count _ _ (restrictLow ok)) (count _ _ (restrictHigh ok)))

theorem hardTree (t : Tree) (ok : ∀ k, ∀ x ∈ sample k, t.run x = k) : 86 ≤ t.leaves := by
  cases t with
  | leaf k =>
    have h := (lowCount (0,0)).trans (count (.leaf k) (low (0,0)) (fun l x hx _ => ok l x hx))
    simp [Tree.leaves] at h
  | query v z o =>
    have hz : Agrees z (low v) := by
      intro k x hx hit
      have hn : bit v x = false := by simpa [low] using hit
      simpa [Tree.run,hn] using ok k x hx
    have ho : Agrees o (high v) := by
      intro k x hx hit
      change bit v x = true at hit
      simpa [Tree.run,hit] using ok k x hx
    exact Nat.add_le_add (lowBranch z v hz) ((highCount v).trans (count o _ ho))

-- The tree may use the same axiom in many places. Each internal node is
-- one actual resolution inference, with the positive parent as its zero child.
inductive RTree : Clause V → Type
  | ax (k : Fin 45) : RTree (axiomAt k)
  | res {C D : Clause V} (v : V) (pos : (v,true) ∈ C) (neg : (v,false) ∈ D)
      (left : RTree C) (right : RTree D) : RTree (C.erase (v,true) ∪ D.erase (v,false))

def RTree.tree {C} : RTree C → Tree
  | .ax k => .leaf k
  | .res v _ _ l r => .query v l.tree r.tree

theorem traceFalse {C} (t : RTree C) (x : ℕ)
    (h : ¬ClauseSat (fun v => bit v x) C) :
    ¬ClauseSat (fun v => bit v x) (axiomAt (t.tree.run x)) := by
  induction t with
  | ax => exact h
  | @res C D v hp hn l r hl hr =>
    cases hv : bit v x
    · simp [RTree.tree,Tree.run,hv]
      apply hl
      rintro ⟨lit,hm,ha⟩
      exact h ⟨lit,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by rintro rfl; simp [hv] at ha,hm⟩),ha⟩
    · simp [RTree.tree,Tree.run,hv]
      apply hr
      rintro ⟨lit,hm,ha⟩
      exact h ⟨lit,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨by rintro rfl; simp [hv] at ha,hm⟩),ha⟩

theorem proofAgrees (t : RTree ∅) (k : Fin 45) (x : ℕ) (hx : x ∈ sample k) : t.tree.run x = k := by
  have hf := (falseIff x _).mpr (traceFalse t x (by simp [ClauseSat]))
  have hs := List.all_eq_true.mp (uniqueFalse k) x hx
  have hr := List.all_eq_true.mp hs (t.tree.run x) (by simp)
  have hk : k = t.tree.run x := by simpa [hf] using hr
  exact hk.symm

/-- At least 85 resolution inferences and all 45 distinct initial clauses. -/
theorem sharedAxiomsBound (t : RTree ∅) : 130 ≤ t.tree.branches + t.tree.names.card := by
  have leaves := hardTree t.tree (proofAgrees t)
  have allNames : t.tree.names = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro k
    have hne : sample k ≠ [] := (by decide : ∀ i : Fin 45, sample i ≠ []) k
    obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil _ hne
    exact proofAgrees t k x hx ▸ mem_names t.tree x
  rw [allNames]
  simp only [Finset.card_univ,Fintype.card_fin]
  have := branches_leaves t.tree
  omega

-- Reflect a proposed decision tree back into the project's binary resolution rule.
def Tree.clause : Tree → Option (Clause V)
  | .leaf k => some (axiomAt k)
  | .query v l r => do
      let C ← l.clause
      let D ← r.clause
      if (v,true) ∈ C ∧ (v,false) ∈ D then some (C.erase (v,true) ∪ D.erase (v,false))
      else none

theorem realize (t : Tree) {C} (ok : t.clause = some C) : ∃ p : RTree C, p.tree = t := by
  induction t generalizing C with
  | leaf k =>
    change some (axiomAt k) = some C at ok
    cases ok
    exact ⟨RTree.ax k,rfl⟩
  | query v l r il ir =>
    cases cl : l.clause with
    | none => simp [Tree.clause,cl] at ok
    | some A =>
      cases cr : r.clause with
      | none => simp [Tree.clause,cl,cr] at ok
      | some B =>
        by_cases h : (v,true) ∈ A ∧ (v,false) ∈ B
        · simp [Tree.clause,cl,cr,h] at ok
          subst C
          obtain ⟨pl,hl⟩ := il cl
          obtain ⟨pr,hr⟩ := ir cr
          exact ⟨RTree.res v h.1 h.2 pl pr,by simp [RTree.tree,hl,hr]⟩
        · simp [Tree.clause,cl,cr,h] at ok

def witness : Tree :=
  .query (0,1)
    (.query (0,2)
     (.query (0,3)
      (.query (0,0)
       (.leaf 0)
       (.query (3,0)
        (.query (1,0)
         (.query (4,0)
          (.query (2,0)
           (.query (3,1)
            (.query (3,3)
             (.query (3,2)
              (.leaf 3)
              (.query (4,2)
               (.query (1,2)
                (.query (2,1)
                 (.query (2,3)
                  (.query (2,2)
                   (.leaf 2)
                   (.leaf 35))
                  (.query (1,1)
                   (.query (1,3)
                    (.leaf 1)
                    (.leaf 24))
                   (.query (4,3)
                    (.query (4,1)
                     (.leaf 4)
                     (.leaf 30))
                    (.leaf 40))))
                 (.query (1,3)
                  (.query (1,1)
                   (.leaf 1)
                   (.leaf 22))
                  (.query (4,3)
                   (.query (4,1)
                    (.leaf 4)
                    (.leaf 38))
                   (.leaf 32))))
                (.leaf 27))
               (.leaf 43)))
             (.query (4,3)
              (.query (1,3)
               (.query (2,1)
                (.query (2,2)
                 (.query (2,3)
                  (.leaf 2)
                  (.leaf 36))
                 (.query (4,1)
                  (.query (4,2)
                   (.leaf 4)
                   (.leaf 39))
                  (.query (1,1)
                   (.query (1,2)
                    (.leaf 1)
                    (.leaf 23))
                   (.leaf 30))))
                (.query (4,2)
                 (.query (4,1)
                  (.leaf 4)
                  (.leaf 38))
                 (.query (1,1)
                  (.query (1,2)
                   (.leaf 1)
                   (.leaf 31))
                  (.leaf 22))))
               (.leaf 28))
              (.leaf 44)))
            (.query (1,1)
             (.query (4,1)
              (.query (2,3)
               (.query (2,2)
                (.query (2,1)
                 (.leaf 2)
                 (.leaf 34))
                (.query (4,3)
                 (.query (4,2)
                  (.leaf 4)
                  (.leaf 39))
                 (.query (1,2)
                  (.query (1,3)
                   (.leaf 1)
                   (.leaf 32))
                  (.leaf 23))))
               (.query (4,3)
                (.query (4,2)
                 (.leaf 4)
                 (.query (1,2)
                  (.query (1,3)
                   (.leaf 1)
                   (.leaf 24))
                  (.leaf 31)))
                (.leaf 40)))
              (.leaf 42))
             (.leaf 26)))
           (.leaf 9))
          (.leaf 17))
         (.leaf 5))
        (.leaf 13)))
      (.query (1,3)
       (.query (2,3)
        (.query (3,3)
         (.query (4,0)
          (.query (4,1)
           (.query (4,2)
            (.query (4,3)
             (.leaf 4)
             (.leaf 20))
            (.query (3,2)
             (.query (2,2)
              (.query (1,0)
               (.query (1,2)
                (.query (1,1)
                 (.leaf 1)
                 (.query (3,0)
                  (.query (3,1)
                   (.leaf 3)
                   (.leaf 26))
                  (.query (2,0)
                   (.query (2,1)
                    (.leaf 2)
                    (.leaf 22))
                   (.leaf 33))))
                (.leaf 31))
               (.query (2,0)
                (.query (3,0)
                 (.query (2,1)
                  (.leaf 2)
                  (.query (3,1)
                   (.leaf 3)
                   (.leaf 34)))
                 (.leaf 25))
                (.leaf 21)))
              (.leaf 39))
             (.leaf 43)))
           (.query (3,1)
            (.query (1,1)
             (.query (2,0)
              (.query (2,2)
               (.query (2,1)
                (.leaf 2)
                (.leaf 38))
               (.query (1,2)
                (.query (1,0)
                 (.leaf 1)
                 (.query (3,0)
                  (.query (3,2)
                   (.leaf 3)
                   (.leaf 35))
                  (.leaf 25)))
                (.leaf 23)))
              (.query (3,0)
               (.query (3,2)
                (.leaf 3)
                (.query (1,0)
                 (.query (1,2)
                  (.leaf 1)
                  (.leaf 27))
                 (.leaf 21)))
               (.leaf 33)))
             (.leaf 30))
            (.leaf 42)))
          (.query (2,0)
           (.query (3,0)
            (.query (1,0)
             (.query (1,1)
              (.query (1,2)
               (.leaf 1)
               (.query (2,2)
                (.query (3,2)
                 (.query (2,1)
                  (.leaf 2)
                  (.query (3,1)
                   (.leaf 3)
                   (.leaf 34)))
                 (.leaf 27))
                (.leaf 23)))
              (.query (2,2)
               (.query (2,1)
                (.leaf 2)
                (.leaf 22))
               (.query (3,1)
                (.query (3,2)
                 (.leaf 3)
                 (.leaf 35))
                (.leaf 26))))
             (.leaf 29))
            (.leaf 41))
           (.leaf 37)))
         (.leaf 16))
        (.leaf 12))
       (.leaf 8)))
     (.query (3,2)
      (.query (4,2)
       (.query (2,2)
        (.query (1,3)
         (.query (1,2)
          (.query (1,0)
           (.query (1,1)
            (.leaf 1)
            (.query (4,1)
             (.query (2,1)
              (.query (3,0)
               (.query (3,1)
                (.query (3,3)
                 (.leaf 3)
                 (.query (2,3)
                  (.query (2,0)
                   (.leaf 2)
                   (.query (4,0)
                    (.query (4,3)
                     (.leaf 4)
                     (.leaf 44))
                    (.leaf 37)))
                  (.leaf 36)))
                (.leaf 26))
               (.query (4,0)
                (.query (2,0)
                 (.query (2,3)
                  (.leaf 2)
                  (.query (4,3)
                   (.leaf 4)
                   (.leaf 40)))
                 (.leaf 33))
                (.leaf 41)))
              (.leaf 22))
             (.leaf 30)))
           (.query (2,0)
            (.query (4,0)
             (.query (3,1)
              (.query (3,0)
               (.query (3,3)
                (.leaf 3)
                (.query (4,1)
                 (.query (4,3)
                  (.leaf 4)
                  (.leaf 44))
                 (.query (2,1)
                  (.query (2,3)
                   (.leaf 2)
                   (.leaf 36))
                  (.leaf 38))))
               (.leaf 25))
              (.query (4,3)
               (.query (4,1)
                (.leaf 4)
                (.leaf 42))
               (.query (2,1)
                (.query (2,3)
                 (.leaf 2)
                 (.leaf 40))
                (.leaf 34))))
             (.leaf 29))
            (.leaf 21)))
          (.leaf 7))
         (.query (2,3)
          (.query (4,3)
           (.query (3,1)
            (.query (3,0)
             (.query (3,3)
              (.leaf 3)
              (.leaf 28))
             (.query (4,1)
              (.query (4,0)
               (.leaf 4)
               (.leaf 41))
              (.query (2,0)
               (.query (2,1)
                (.leaf 2)
                (.leaf 38))
               (.leaf 33))))
            (.query (2,0)
             (.query (2,1)
              (.leaf 2)
              (.leaf 34))
             (.query (4,0)
              (.query (4,1)
               (.leaf 4)
               (.leaf 42))
              (.leaf 37))))
           (.leaf 32))
          (.leaf 24)))
        (.leaf 11))
       (.leaf 19))
      (.leaf 15)))
    (.query (3,1)
     (.query (2,1)
      (.query (1,1)
       (.query (4,0)
        (.query (4,3)
         (.query (4,1)
          (.query (4,2)
           (.leaf 4)
           (.query (1,2)
            (.query (3,2)
             (.query (2,0)
              (.query (2,3)
               (.query (2,2)
                (.leaf 2)
                (.leaf 39))
               (.query (3,3)
                (.query (1,3)
                 (.query (3,0)
                  (.leaf 3)
                  (.query (1,0)
                   (.leaf 1)
                   (.leaf 25)))
                 (.leaf 24))
                (.leaf 36)))
              (.query (3,0)
               (.query (3,3)
                (.leaf 3)
                (.query (1,0)
                 (.query (1,3)
                  (.leaf 1)
                  (.leaf 28))
                 (.leaf 21)))
               (.leaf 33)))
             (.leaf 43))
            (.leaf 31)))
          (.leaf 18))
         (.query (1,3)
          (.query (3,3)
           (.query (2,0)
            (.query (2,2)
             (.query (2,3)
              (.leaf 2)
              (.leaf 40))
             (.query (3,2)
              (.query (1,0)
               (.query (1,2)
                (.leaf 1)
                (.leaf 23))
               (.query (3,0)
                (.leaf 3)
                (.leaf 25)))
              (.leaf 35)))
            (.query (3,0)
             (.query (1,2)
              (.query (1,0)
               (.leaf 1)
               (.leaf 21))
              (.query (3,2)
               (.leaf 3)
               (.leaf 27)))
             (.leaf 33)))
           (.leaf 44))
          (.leaf 32)))
        (.query (2,0)
         (.query (3,0)
          (.query (1,3)
           (.query (1,0)
            (.query (1,2)
             (.leaf 1)
             (.query (3,2)
              (.query (2,2)
               (.query (3,3)
                (.leaf 3)
                (.query (2,3)
                 (.leaf 2)
                 (.leaf 36)))
               (.leaf 23))
              (.leaf 27)))
            (.leaf 29))
           (.query (2,3)
            (.query (3,2)
             (.query (3,3)
              (.leaf 3)
              (.leaf 28))
             (.query (2,2)
              (.leaf 2)
              (.leaf 35)))
            (.leaf 24)))
          (.leaf 41))
         (.leaf 37)))
       (.leaf 6))
      (.leaf 10))
     (.leaf 14))

theorem witnessChecks : witness.clause = some ∅ ∧ witness.branches = 188 ∧ witness.names.card = 45 := by
  decide +kernel

theorem attainable : ∃ p : RTree ∅, p.tree.branches = 188 ∧ p.tree.names.card = 45 := by
  obtain ⟨p,hp⟩ := realize witness witnessChecks.1
  exact ⟨p,hp ▸ witnessChecks.2⟩

theorem validAxioms : ∀ C ∈ axiomList, C ∈ PHP 5 4 := by
  intro C hC
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hC
  have claim : ∀ k : Fin 45, (∃ p : Fin 5, axiomAt k = row p) ∨
      ∃ p q : Fin 5, ∃ h : Fin 4, p ≠ q ∧ axiomAt k = collision p q h := by decide
  exact claim ⟨i,hi⟩

theorem axBase (xs : List (Clause V)) (all : ∀ C ∈ xs, C ∈ PHP 5 4) :
    IsDerivation (PHP 5 4) xs := by
  induction xs with
  | nil => exact .nil
  | cons C cs ih => exact .ax (ih (fun c hc => all c (List.mem_cons_of_mem _ hc))) (all _ List.mem_cons_self)

def RTree.emit {C : Clause V} : RTree C → List (Clause V)
  | .ax _ => []
  | @RTree.res A B v _ _ l r => (A.erase (v,true) ∪ B.erase (v,false)) :: (r.emit ++ l.emit)

theorem emitLength {C} (p : RTree C) : p.emit.length = p.tree.branches := by
  induction p with
  | ax => rfl
  | res _ _ _ _ _ hl hr => simp [RTree.emit,RTree.tree,Tree.branches,hl,hr,Nat.add_comm]

theorem appendProof {C} (p : RTree C) (base : List (Clause V)) (hb : IsDerivation (PHP 5 4) base)
    (supports : ∀ k, axiomAt k ∈ base) :
    IsDerivation (PHP 5 4) (p.emit ++ base) ∧ C ∈ p.emit ++ base := by
  induction p generalizing base with
  | ax k => exact ⟨hb,supports k⟩
  | @res C D v hp hn l r il ir =>
    obtain ⟨h1,mem1⟩ := il base hb supports
    obtain ⟨h2,mem2⟩ := ir _ h1 (fun k => List.mem_append_right _ (supports k))
    simp only [RTree.emit,List.cons_append,List.append_assoc]
    exact ⟨.res h2 (List.mem_append_right _ mem1) mem2 ⟨v,hp,hn,rfl⟩,List.mem_cons_self⟩

theorem listedWitness : ∃ π, IsRefutation (PHP 5 4) π ∧ π.length = 233 := by
  obtain ⟨p,hp,_⟩ := attainable
  obtain ⟨der,member⟩ := appendProof p axiomList (axBase _ validAxioms)
    (fun k => List.getElem_mem (l:=axiomList) (n:=k.val) (by exact k.isLt))
  refine ⟨p.emit ++ axiomList,⟨der,member⟩,?_⟩
  rw [List.length_append,emitLength,hp]
  rfl

end TreeResolution
