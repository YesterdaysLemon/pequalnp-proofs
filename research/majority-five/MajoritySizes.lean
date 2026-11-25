import MajorityLower
import SplitMonotone
import BinaryWireCost

namespace FiveMajority
open Paired Paired.Split PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def nine : BinaryCircuit := ⟨[
  ⟨(· ^^ ·),0,1⟩, ⟨(· ^^ ·),0,2⟩, ⟨(· ^^ ·),2,5⟩,
  ⟨(· ^^ ·),3,4⟩, ⟨(· ^^ ·),3,7⟩, ⟨(· || ·),5,6⟩,
  ⟨(· || ·),8,9⟩, ⟨(· && ·),10,11⟩, ⟨(· ^^ ·),7,12⟩],13⟩

def ten : Circuit := ⟨[
  ⟨.and,[0,1]⟩, ⟨.or,[0,1]⟩, ⟨.and,[2,3]⟩, ⟨.or,[2,3]⟩,
  ⟨.or,[5,7]⟩, ⟨.and,[4,9]⟩, ⟨.or,[4,9]⟩, ⟨.and,[6,8]⟩,
  ⟨.or,[10,12]⟩, ⟨.and,[11,13]⟩],14⟩

theorem nine_eval (x : Row) : nine.eval (keys.map x) = fn x := by
  have table : ∀ v : Fin 5 → Bool, nine.eval (List.ofFn v) = vote v := by decide +kernel
  simpa [keys,fn] using table (fun i => x (coord i))

theorem ten_eval (x : Row) : ten.eval (keys.map x) = fn x := by
  have table : ∀ v : Fin 5 → Bool, ten.eval (List.ofFn v) = vote v := by decide +kernel
  simpa [keys,fn] using table (fun i => x (coord i))

theorem ten_mono : Monotone2 ten := by
  intro g hg
  change (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2
  simp only [ten,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem full_size (k : Nat) : native keys fn k ↔ 9 ≤ k := by
  constructor
  · rintro ⟨C,bound,ev⟩
    exact (root_lower true (FirstGate.of_circuit keys fn C (fun _ _ => .inl rfl) ev nonzero)).trans bound
  · intro bound
    exact ⟨nine,(cost_le nine).trans (show nine.size ≤ k from bound),nine_eval⟩

def signed (k : Nat) : Prop :=
  ∃ C : BinaryCircuit, (∀ g ∈ C.gates, FirstGate.parity g.op = false) ∧
    cost C ≤ k ∧ ∀ x : Row, C.eval (keys.map x) = fn x

theorem signed_size (k : Nat) : signed k ↔ 10 ≤ k := by
  constructor
  · rintro ⟨C,allow,bound,ev⟩
    exact (root_lower false (FirstGate.of_circuit keys fn C (fun g h => .inr (allow g h)) ev nonzero)).trans bound
  · intro bound
    refine ⟨translate ten,?_,?_,?_⟩
    · intro g hg
      simp only [translate,ten,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · have small := cost_le (translate ten)
      rw [translate_size] at small
      exact small.trans (show ten.size ≤ k from bound)
    · intro x
      exact (translate_eval ten (fun g h => (ten_mono g h).2) _).trans (ten_eval x)

theorem translated_parity (C : Circuit) (mono : Monotone2 C) :
    ∀ g ∈ (translate C).gates, FirstGate.parity g.op = false := by
  intro g hg
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
  obtain ⟨kind,arity⟩ := mono a ha
  obtain ⟨op,args⟩ := a
  change op = .and ∨ op = .or at kind
  change args.length ≤ 2 at arity
  rcases args with _|⟨i,_|⟨j,_|⟨h,t⟩⟩⟩ <;> simp at arity
  all_goals rcases kind with rfl | rfl <;> rfl

theorem monotone_size (k : Nat) : mono keys fn k ↔ 10 ≤ k := by
  constructor
  · rintro ⟨C,legal,bound,ev⟩
    apply (signed_size k).mp
    refine ⟨translate C,translated_parity C legal,?_,fun x => (translate_eval C (fun g h => (legal g h).2) _).trans (ev x)⟩
    exact (cost_le (translate C)).trans ((translate_size C) ▸ bound)
  · intro bound
    exact ⟨ten,ten_mono,bound,ten_eval⟩

theorem listed_size (k : Nat) : listed keys fn k ↔ 9 ≤ k := by
  constructor
  · rintro ⟨C,bound,ev⟩
    exact (full_size k).mp ⟨C,(cost_le C).trans bound,ev⟩
  · intro bound
    exact ⟨nine,bound,nine_eval⟩

end FiveMajority
