import PairedUpper

/-! Exact size in the native project interfaces, with interleaved input order. -/
namespace Paired
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def translateGate (g : Gate) : BinaryGate :=
  match g.inputs with
  | [] => ⟨fun _ _ => g.op.eval [],0,0⟩
  | [i] => ⟨fun a _ => g.op.eval [a],i,i⟩
  | i :: j :: _ => ⟨fun a b => g.op.eval [a,b],i,j⟩

def translate (C : Circuit) : BinaryCircuit := ⟨C.gates.map translateGate,C.output⟩

theorem translate_step (g : Gate) (arity : g.inputs.length ≤ 2) (w : List Bool) :
    bitStep w (translateGate g) = Formula.applyGate w g := by
  obtain ⟨op,ins⟩ := g
  rcases ins with _ | ⟨i,_ | ⟨j,_ | ⟨k,rest⟩⟩⟩ <;>
    first | rfl | simp at arity

theorem translate_eval (C : Circuit) (arity : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (w : List Bool) :
    (translate C).eval w = C.eval w := by
  have same (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) (v : List Bool) :
      (gs.map translateGate).foldl bitStep v = gs.foldl Formula.applyGate v := by
    induction gs generalizing v with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.map_cons,List.foldl_cons,translate_step g (h g (by simp))]
      exact ih (fun z hz => h z (by simp [hz])) _
  exact congrArg (fun l : List Bool => l.getD C.output false) (same C.gates arity w)

theorem translate_size (C : Circuit) : (translate C).size = C.size := List.length_map ..

theorem cost_le (C : BinaryCircuit) : cost C ≤ C.size := List.length_filter_le ..

theorem labels_succ (n : ℕ) : labels (n+1) = labels n ++ [(n,false),(n,true)] := by
  simp [labels,List.range_succ]

theorem labels_length (n : ℕ) : (labels n).length = 2*n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [labels_succ,List.length_append,ih]; simp; omega

theorem labels_nodup (n : ℕ) : (labels n).Nodup := by
  induction n with
  | zero => simp [labels]
  | succ n ih =>
    rw [labels_succ,List.nodup_append]
    refine ⟨ih,by simp,?_⟩
    intro a ha b hb
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
    have h := (label_mem n a).mp ha
    rcases hb with rfl | rfl <;> rintro rfl <;> omega

def decode (n : ℕ) (v : List Bool) (p : Coord) : Bool := v.getD ((labels n).idxOf p) false

noncomputable def onFin (n : ℕ) (x : Fin (2*n) → Bool) : Bool :=
  value (Finset.range n) (decode n (List.ofFn x))

theorem decode_map {n : ℕ} (x : Row) {p : Coord} (hp : p.1 < n) :
    decode n ((labels n).map x) p = x p := by
  have b := List.idxOf_lt_length_of_mem ((label_mem n p).mpr hp)
  unfold decode
  rw [List.getD_eq_getElem _ _ (by simpa using b),List.getElem_map,List.getElem_idxOf]

theorem map_decode {n : ℕ} (v : List Bool) (len : v.length = 2*n) :
    (labels n).map (decode n v) = v := by
  apply List.ext_getElem (by simp [labels_length,len])
  intro i hi hv
  have hl : i < (labels n).length := by simpa using hi
  simp only [List.getElem_map,decode,(labels_nodup n).idxOf_getElem i hl,
    List.getD_eq_getElem _ _ hv]

theorem value_congr (s : Finset ℕ) (x y : Row) (h : ∀ i ∈ s, ∀ b, x (i,b) = y (i,b)) :
    value s x = value s y := by
  have go (a b : Row) (ha : ∀ i ∈ s, ∀ t, a (i,t) = b (i,t))
      (yes : value s a = true) : value s b = true := by
    apply decide_eq_true
    rcases of_decide_eq_true yes with all | ⟨i,hi,l,r⟩
    · exact .inl fun i hi => (ha i hi false).symm.trans (all i hi)
    · exact .inr ⟨i,hi,(ha i hi false).symm.trans l,(ha i hi true).symm.trans r⟩
  exact Bool.eq_iff_iff.mpr ⟨go x y h,go y x (fun i hi t => (h i hi t).symm)⟩

theorem list_ofFn_read {k : ℕ} (v : List Bool) (len : v.length = k) :
    List.ofFn (fun i : Fin k => v.getD i false) = v := by
  apply List.ext_getElem (by simp [len])
  intro i _ hv
  simp only [List.getElem_ofFn,List.getD_eq_getElem _ _ hv]

theorem lift_computes {n : ℕ} {ev : List Bool → Bool}
    (h : ∀ x, ev (List.ofFn x) = onFin n x) (y : Row) :
    ev ((labels n).map y) = value (Finset.range n) y := by
  let v := (labels n).map y
  let x := fun i : Fin (2*n) => v.getD i false
  have e : List.ofFn x = v := list_ofFn_read v (by simp [v,labels_length])
  have eq := h x
  change ev (List.ofFn x) = value _ (decode n (List.ofFn x)) at eq
  rw [e] at eq
  exact eq.trans (value_congr _ _ y (fun i hi t => decode_map y (p := (i,t)) (Finset.mem_range.mp hi)))

theorem finite_upper {n : ℕ} (hn : 2 ≤ n) :
    ∃ C : Circuit, Monotone2 C ∧ C.size + 2 = 3*n ∧
      ∀ x : Fin (2*n) → Bool, C.eval (List.ofFn x) = onFin n x := by
  obtain ⟨C,ok,size,corr⟩ := monotone_upper n hn
  refine ⟨C,ok,size,?_⟩
  intro x
  have eq := corr (decode n (List.ofFn x))
  rwa [map_decode _ (List.length_ofFn ..)] at eq

theorem binary_size_iff {n s : ℕ} (hn : 2 ≤ n) :
    HasBinarySize (2*n) (onFin n) s ↔ 3*n ≤ s + 2 := by
  constructor
  · rintro ⟨C,size,eval⟩
    have b := circuit_lower hn C (lift_computes eval)
    have c := cost_le C
    omega
  · intro b
    obtain ⟨C,ok,size,eval⟩ := finite_upper hn
    refine ⟨translate C,by rw [translate_size]; omega,?_⟩
    intro x
    exact (translate_eval C (fun g hg => (ok g hg).2) _).trans (eval x)

theorem monotone_replacement {n s : ℕ} (hn : 2 ≤ n) (h : HasCircuitSize (2*n) (onFin n) s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin (2*n) → Bool, C.eval (List.ofFn x) = onFin n x := by
  obtain ⟨D,ok,bd,hd⟩ := h
  have binary : HasBinarySize (2*n) (onFin n) s :=
    ⟨translate D,(translate_size D).le.trans bd,fun x =>
      (translate_eval D (fun g hg => (ok g hg).2) _).trans (hd x)⟩
  have low := (binary_size_iff hn).mp binary
  obtain ⟨C,mono,size,ev⟩ := finite_upper hn
  exact ⟨C,mono,by omega,ev⟩

end Paired
