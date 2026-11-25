import KWEncoding
import Mathlib.Data.List.Count

namespace KWEncoding
open Std.Sat

structure Selection (g : Game) (budget : Nat) where
  picked : Nat → Bool
  active : Nat → Nat → Bool
  enabled : ∀ p < g.patterns, ∀ j < g.cols, g.col p j = true → active p j = true → picked p = true
  cover : ∀ i < g.rows, ∀ j < g.cols, ∃ p ∈ options g i j, active p j = true
  unique : ∀ i < g.rows, ∀ j < g.cols, ∀ p ∈ options g i j, ∀ q ∈ options g i j,
    active p j = true → active q j = true → p=q
  size : (List.range g.patterns).countP picked ≤ budget

def prefixCount (s : Nat → Bool) (i : Nat) := (List.range i).countP s

theorem prefix_succ (s : Nat → Bool) (i : Nat) :
    prefixCount s (i+1) = prefixCount s i + if s i then 1 else 0 := by
  simp [prefixCount,List.range_succ,List.countP_append]

def assignment {g b} (s : Selection g b) : Var → Bool
  | .select p => s.picked p
  | .use p j => s.active p j
  | .count i t => decide (t ≤ prefixCount s.picked i)

def holds (a : Var → Bool) (c : Raw) := ∃ l ∈ c, a l.1 = l.2

theorem counter_ok {g b} (s : Selection g b) (i : Nat) (c : Raw) (mem : c ∈ counterStep b i) :
    holds (assignment s) c := by
  simp only [counterStep,List.mem_append,List.mem_singleton,List.mem_map] at mem
  rcases mem with (rfl | ⟨t,_,rfl⟩) | ⟨t,_,rfl⟩
  all_goals cases h : s.picked i <;> simp [holds,pos,neg,assignment,prefix_succ,h] <;> omega

theorem cardinal_ok {g b} (s : Selection g b) (c : Raw) (mem : c ∈ cardinal g.patterns b) :
    holds (assignment s) c := by
  simp only [cardinal,List.mem_append,List.mem_singleton,List.mem_map,List.mem_flatMap] at mem
  rcases mem with (⟨t,_,rfl⟩ | ⟨i,_,hi⟩) | rfl
  · simp [holds,neg,assignment,prefixCount]
  · exact counter_ok s i c hi
  · have bd := s.size
    refine ⟨neg (.count g.patterns (b+1)),by simp,?_⟩
    change decide (b+1 ≤ (List.range g.patterns).countP s.picked) = false
    rw [decide_eq_false_iff_not]
    omega

theorem access_ok {g b} (s : Selection g b) {c : Raw} (mem : c ∈ access g) : holds (assignment s) c := by
  simp only [access,List.mem_flatMap,List.mem_range,List.mem_map,List.mem_filter] at mem
  obtain ⟨p,hp,j,⟨hj,col⟩,rfl⟩ := mem
  cases hit : s.active p j with
  | false => simp [holds,neg,pos,assignment,hit]
  | true => simp [holds,neg,pos,assignment,s.enabled p hp j hj col hit]

theorem cell_ok {g b} (s : Selection g b) {i j : Nat} (hi : i<g.rows) (hj : j<g.cols)
    {c : Raw} (mem : c ∈ cell g i j) : holds (assignment s) c := by
  simp only [cell,List.mem_cons,List.mem_flatMap,List.mem_map,List.mem_filter,decide_eq_true_eq] at mem
  rcases mem with rfl | ⟨p,hp,q,⟨hq,lt⟩,rfl⟩
  · obtain ⟨p,hp,ok⟩ := s.cover i hi j hj
    exact ⟨pos (.use p j),List.mem_map.mpr ⟨p,hp,rfl⟩,ok⟩
  · cases a : s.active p j <;> cases d : s.active q j <;> simp [holds,neg,assignment,a,d]
    have eq := s.unique i hi j hj p hp q hq a d
    omega

theorem true_named {g b} (s : Selection g b) : (named g b).eval (assignment s) = true := by
  have every (c : Raw) (hc : c ∈ raw g b) : holds (assignment s) c := by
    simp only [raw,List.mem_append,List.mem_flatMap,List.mem_range] at hc
    rcases hc with (first | ⟨i,hi,j,hj,cell⟩) | last
    · exact access_ok s first
    · exact cell_ok s hi hj cell
    · exact cardinal_ok s c last
  apply Array.all_eq_true_iff_forall_mem.mpr
  intro c h
  change c ∈ ((raw g b).map CNF.Clause.ofLiterals).toArray at h
  simp only [List.mem_toArray,List.mem_map] at h
  obtain ⟨a,ha,rfl⟩ := h
  obtain ⟨l,hl,eq⟩ := every a ha
  exact List.any_eq_true.mpr ⟨l,by simpa using hl,by simpa using eq⟩

theorem impossible {g b} (bad : (problem g b).Unsat) (s : Selection g b) : False := by
  have u := (CNF.unsat_relabel_iff (f := named g b) (r := code) (fun _ _ h => code_injective h)).mp bad
  have contra := u (assignment s)
  rw [true_named s] at contra
  cases contra

end KWEncoding
