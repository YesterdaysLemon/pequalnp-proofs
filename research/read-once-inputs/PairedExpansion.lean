import SplitMonotone

namespace Paired.Split
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

-- At each step any current primary input can be replaced by its AND or OR with a fresh input.
inductive Expansion (n : ℕ) : List Coord → Wire → ℕ → Prop where
  | base : Expansion n (labels n) (value (Finset.range n)) 0
  | step {keys f d p q} (h : Expansion n keys f d) (pIn : p ∈ keys) (fresh : q ∉ keys) (t : Bool) :
      Expansion n (q::keys) (split f t p q) (d+1)

theorem base_supported (n : ℕ) : supported (labels n).toFinset (value (Finset.range n)) := by
  intro x y eq
  apply value_congr
  intro i hi t
  exact eq _ (List.mem_toFinset.mpr ((label_mem n _).mpr (Finset.mem_range.mp hi)))

theorem base_essential {n : ℕ} (hn : 2 ≤ n) {p : Coord} (hp : p ∈ labels n) :
    essential (value (Finset.range n)) p := by
  let s := Finset.range n
  have hs : 2 ≤ s.card := by simpa [s] using hn
  have ip : p.1 ∈ s := Finset.mem_range.mpr ((label_mem n p).mp hp)
  obtain ⟨x,y,diff,eq,out⟩ := pair_separates hs p (mate p) ip ip (Ne.symm (mate_ne p)) (fun _ b => b)
  refine ⟨physical x,physical y,?_,?_⟩
  · rw [value_complement,value_complement]
    intro same
    have orig := congrArg Bool.not same
    simp only [Bool.not_not] at orig
    exact diff orig
  · intro i ne
    have same : x i = y i := by
      by_cases e : i = mate p
      · exact e ▸ eq
      · exact out i ne e
    simp only [physical,same]

theorem expansion_inputs {n : ℕ} (hn : 2 ≤ n) {keys : List Coord} {f : Wire} {d : ℕ}
    (e : Expansion n keys f d) :
    keys.Nodup ∧ supported keys.toFinset f ∧ ∀ p ∈ keys, essential f p := by
  induction e with
  | base => exact ⟨labels_nodup n,base_supported n,fun _ hp => base_essential hn hp⟩
  | @step keys f d p q _ hp fresh t ih =>
    obtain ⟨nd,sup,all⟩ := ih
    have hq : q ∉ keys.toFinset := by simpa using fresh
    refine ⟨List.nodup_cons.mpr ⟨fresh,nd⟩,?_,?_⟩
    · simpa only [List.toFinset_cons] using support_split sup (List.mem_toFinset.mpr hp) (q := q) t
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | old
      · exact fresh_essential sup (List.mem_toFinset.mpr hp) hq t (all _ hp)
      · exact preserve_essential sup hq t (all _ old)

theorem central_native {n k : ℕ} (hn : 2 ≤ n) :
    native (labels n) (value (Finset.range n)) k ↔ 3*n ≤ k+2 := by
  constructor
  · rintro ⟨C,bd,ev⟩
    have l := circuit_lower hn C ev
    omega
  · intro lower
    obtain ⟨C,ok,size,ev⟩ := monotone_upper n hn
    refine ⟨translate C,?_,fun x => (translate_eval _ (fun g hg => (ok g hg).2) _).trans (ev x)⟩
    have cost := cost_le (translate C)
    rw [translate_size] at cost
    omega

theorem exact_native {n : ℕ} (hn : 2 ≤ n) {keys : List Coord} {f : Wire} {d : ℕ}
    (e : Expansion n keys f d) (k : ℕ) : native keys f k ↔ 3*n+d ≤ k+2 := by
  induction e generalizing k with
  | base => simpa using (central_native (k := k) hn)
  | @step keys f d p q e hp fresh t ih =>
    obtain ⟨_,sup,all⟩ := expansion_inputs hn e
    have ess := all p hp
    cases k with
    | succ k =>
      rw [native_split_iff keys sup hp fresh t ess k,ih]
      omega
    | zero =>
      constructor
      · intro h
        have hq : q ∉ keys.toFinset := by simpa using fresh
        have nz := nonzero_of_essential (fresh_essential sup (List.mem_toFinset.mpr hp) hq t ess)
        have run := (native_iff _ _ _ nz).mp h
        rw [List.toFinset_cons] at run
        obtain ⟨l,bd,_⟩ := split_lower sup (List.mem_toFinset.mpr hp) hq t ess run
        omega
      · omega

theorem exact_monotone {n : ℕ} (hn : 2 ≤ n) {keys : List Coord} {f : Wire} {d : ℕ}
    (e : Expansion n keys f d) : mono keys f (3*n+d-2) := by
  induction e with
  | base =>
    obtain ⟨C,ok,size,ev⟩ := monotone_upper n hn
    exact ⟨C,ok,by omega,ev⟩
  | @step keys f d p q e hp fresh t ih =>
    have next := mono_split (expansion_inputs hn e).1 hp q t ih
    convert next using 1; omega

theorem expansion_length {n : ℕ} {keys : List Coord} {f : Wire} {d : ℕ}
    (e : Expansion n keys f d) : keys.length = 2*n+d := by
  induction e with
  | base => simp [labels_length]
  | step _ _ _ _ ih => simp only [List.length_cons,ih]; omega

end Paired.Split
