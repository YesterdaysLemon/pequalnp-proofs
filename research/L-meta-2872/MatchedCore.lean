import PEqualNP.Defs

namespace MatchedCore

variable {P L : Type*} [DecidableEq P] [DecidableEq L]

def matching (M : Finset (P × L)) : Prop :=
  (∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f) ∧
  (∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f)

def c4free (E : Finset (P × L)) : Prop :=
  ∀ p q : P, ∀ l k : L, p ≠ q → l ≠ k →
    ¬ ((p,l) ∈ E ∧ (p,k) ∈ E ∧ (q,l) ∈ E ∧ (q,k) ∈ E)

def points (M : Finset (P × L)) := M.image Prod.fst
def lines (M : Finset (P × L)) := M.image Prod.snd

theorem insertMatching {M : Finset (P × L)} (m : matching M) {u : P × L}
    (row : u.1 ∉ points M) (col : u.2 ∉ lines M) : matching (insert u M) := by
  have rowNe (e) (he : e ∈ M) : u.1 ≠ e.1 := by
    intro eq
    exact row (eq ▸ Finset.mem_image_of_mem Prod.fst he)
  have colNe (e) (he : e ∈ M) : u.2 ≠ e.2 := by
    intro eq
    exact col (eq ▸ Finset.mem_image_of_mem Prod.snd he)
  constructor
  · intro e he f hf eq
    rcases Finset.mem_insert.mp he with eu | eM
    · subst e
      rcases Finset.mem_insert.mp hf with fu | fM
      · exact fu.symm
      · exact (rowNe _ fM eq).elim
    · rcases Finset.mem_insert.mp hf with fu | fM
      · subst f
        exact (rowNe _ eM eq.symm).elim
      · exact m.1 _ eM _ fM eq
  · intro e he f hf eq
    rcases Finset.mem_insert.mp he with eu | eM
    · subst e
      rcases Finset.mem_insert.mp hf with fu | fM
      · exact fu.symm
      · exact (colNe _ fM eq).elim
    · rcases Finset.mem_insert.mp hf with fu | fM
      · subst f
        exact (colNe _ eM eq.symm).elim
      · exact m.2 _ eM _ fM eq

theorem covers {E M : Finset (P × L)} (sub : M ⊆ E) (m : matching M)
    (maximum : ∀ T ⊆ E, matching T → T.card ≤ M.card) :
    ∀ e ∈ E, e.1 ∈ points M ∨ e.2 ∈ lines M := by
  intro e he
  by_contra! misses
  have fresh : e ∉ M := fun h => misses.1 (Finset.mem_image_of_mem Prod.fst h)
  have bigger := maximum (insert e M) (Finset.insert_subset he sub)
    (insertMatching m misses.1 misses.2)
  rw [Finset.card_insert_of_notMem fresh] at bigger
  omega

theorem onlyLeaves {E M : Finset (P × L)} (sq : c4free E)
    (cover : ∀ e ∈ E, e.1 ∈ points M ∨ e.2 ∈ lines M)
    (meetL : ∀ l ∈ lines M, ∀ k ∈ lines M, l ≠ k →
      ∃ p ∈ points M, (p,l) ∈ E ∧ (p,k) ∈ E)
    (meetP : ∀ p ∈ points M, ∀ q ∈ points M, p ≠ q →
      ∃ l ∈ lines M, (p,l) ∈ E ∧ (q,l) ∈ E) :
    (∀ p ∉ points M, ∀ l k, (p,l) ∈ E → (p,k) ∈ E → l = k) ∧
    (∀ l ∉ lines M, ∀ p q, (p,l) ∈ E → (q,l) ∈ E → p = q) := by
  constructor
  · intro p out l k hl hk
    by_contra ne
    obtain ⟨q,hq,ql,qk⟩ := meetL l ((cover _ hl).resolve_left out)
      k ((cover _ hk).resolve_left out) ne
    exact sq p q l k (fun e => out (e ▸ hq)) ne ⟨hl,hk,ql,qk⟩
  · intro l out p q hp hq
    by_contra ne
    obtain ⟨k,hk,pk,qk⟩ := meetP p ((cover _ hp).resolve_right out)
      q ((cover _ hq).resolve_right out) ne
    exact sq p q l k ne (fun e => out (e ▸ hk)) ⟨hp,pk,hq,qk⟩

-- The alternating six-cycle supplies both common-neighbor hypotheses.
def ring (p l : Fin 3) : Prop := p = l ∨ p = l+1

theorem ringPointsMeet : ∀ p q : Fin 3, ∃ l, ring p l ∧ ring q l := by
  unfold ring
  decide
theorem ringLinesMeet : ∀ l k : Fin 3, ∃ p, ring p l ∧ ring p k := by
  unfold ring
  decide

private theorem missingChord : ∀ i j : Fin 3, ¬ring i j →
    ∃ k d, i ≠ k ∧ j ≠ d ∧ ring i d ∧ ring k j ∧ ring k d := by
  unfold ring
  decide

def diag (a : Fin 3 → P) (b : Fin 3 → L) : Finset (P × L) :=
  Finset.univ.image fun i => (a i,b i)

theorem sixCycleStructure {E : Finset (P × L)} (sq : c4free E)
    (a : Fin 3 → P) (b : Fin 3 → L) (ai : Function.Injective a) (bi : Function.Injective b)
    (cycle : ∀ i j, ring i j → (a i,b j) ∈ E)
    (maximum : ∀ T ⊆ E, matching T → T.card ≤ 3) :
    (∀ i j, (a i,b j) ∈ E ↔ ring i j) ∧
    (∀ e ∈ E, e.1 ∈ points (diag a b) ∨ e.2 ∈ lines (diag a b)) ∧
    (∀ p ∉ points (diag a b), ∀ l k, (p,l) ∈ E → (p,k) ∈ E → l = k) ∧
    (∀ l ∉ lines (diag a b), ∀ p q, (p,l) ∈ E → (q,l) ∈ E → p = q) := by
  have sub : diag a b ⊆ E := by
    intro e he
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
    exact cycle i i (Or.inl rfl)
  have mat : matching (diag a b) := by
    constructor <;> intro e he f hf eq <;>
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he <;>
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hf
    · exact congrArg (fun v => (a v,b v)) (ai eq)
    · exact congrArg (fun v => (a v,b v)) (bi eq)
  have card : (diag a b).card = 3 := by
    rw [diag,Finset.card_image_of_injective _ (fun _ _ h => ai (congrArg Prod.fst h))]
    decide
  have cov := covers sub mat (fun t ht mt => card ▸ maximum t ht mt)
  have inP (p) : p ∈ points (diag a b) ↔ ∃ i, a i = p := by
    simp [points,diag,Finset.image_image,Function.comp_def]
  have inL (l) : l ∈ lines (diag a b) ↔ ∃ i, b i = l := by
    simp [lines,diag,Finset.image_image,Function.comp_def]
  have leaf := onlyLeaves sq cov (by
    intro l hl k hk _
    obtain ⟨i,rfl⟩ := (inL _).1 hl
    obtain ⟨j,rfl⟩ := (inL _).1 hk
    obtain ⟨p,pi,pj⟩ := ringLinesMeet i j
    exact ⟨a p,(inP _).2 ⟨p,rfl⟩,cycle _ _ pi,cycle _ _ pj⟩) (by
    intro p hp q hq _
    obtain ⟨i,rfl⟩ := (inP _).1 hp
    obtain ⟨j,rfl⟩ := (inP _).1 hq
    obtain ⟨l,il,jl⟩ := ringPointsMeet i j
    exact ⟨b l,(inL _).2 ⟨l,rfl⟩,cycle _ _ il,cycle _ _ jl⟩)
  refine ⟨?_,cov,leaf⟩
  intro i j
  constructor
  · intro e
    by_contra hn
    obtain ⟨k,d,ik,jd,id,kj,kd⟩ := missingChord i j hn
    exact sq (a i) (a k) (b j) (b d) (ai.ne ik) (bi.ne jd)
      ⟨e,cycle _ _ id,cycle _ _ kj,cycle _ _ kd⟩
  · exact cycle i j

end MatchedCore
