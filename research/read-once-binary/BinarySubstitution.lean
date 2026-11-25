import EssentialRestrictions

namespace Paired.Split

-- A nondegenerate Boolean gate has an invertible unary section in each direction.
theorem left_section : ∀ o : Op, both o = true → ∃ b s : Bool, ∀ a : Bool, o (a ^^ s) b = a := by
  decide +kernel

theorem right_section : ∀ o : Op, both o = true → ∃ a s : Bool, ∀ b : Bool, o a (b ^^ s) = b := by
  decide +kernel

noncomputable section
open Classical LiveRestriction

def subRow (o : Op) (p q : Coord) (x : Row) : Row :=
  Function.update x p (o (x p) (x q))

def composeInput (f : Wire) (o : Op) (p q : Coord) : Wire := f ∘ subRow o p q

def leftRow (p q : Coord) (b sign : Bool) (x : Row) : Row := fun i =>
  if i = p then x p ^^ sign else if i = q then b else x i

def rightRow (p q : Coord) (a sign : Bool) (x : Row) : Row := fun i =>
  if i = p then a else if i = q then x p ^^ sign else x i

theorem left_recovers {s : Finset Coord} {f : Wire} (sup : supported s f)
    {p q : Coord} (pq : p ≠ q) (fresh : q ∉ s) {o : Op} {b sign : Bool}
    (sectionEq : ∀ a : Bool, o (a ^^ sign) b = a) (x : Row) :
    composeInput f o p q (leftRow p q b sign x) = f x := by
  apply sup
  intro i hi
  by_cases ip : i = p
  · subst i
    simp [subRow,leftRow,Ne.symm pq,sectionEq]
  · have iq : i ≠ q := fun e => fresh (e ▸ hi)
    simp [subRow,leftRow,ip,iq]

theorem right_recovers {s : Finset Coord} {f : Wire} (sup : supported s f)
    {p q : Coord} (pq : p ≠ q) (fresh : q ∉ s) {o : Op} {a sign : Bool}
    (sectionEq : ∀ b : Bool, o a (b ^^ sign) = b) (x : Row) :
    composeInput f o p q (rightRow p q a sign x) = f x := by
  apply sup
  intro i hi
  by_cases ip : i = p
  · subst i
    simp [subRow,rightRow,Ne.symm pq,sectionEq]
  · have iq : i ≠ q := fun e => fresh (e ▸ hi)
    simp [subRow,rightRow,ip,iq]

theorem compose_supported {s : Finset Coord} {f : Wire} (sup : supported s f)
    {p q : Coord} (hp : p ∈ s) (o : Op) : supported (insert q s) (composeInput f o p q) := by
  intro x y same
  apply sup
  intro i hi
  by_cases ip : i = p
  · subst i
    simp [subRow,same p (Finset.mem_insert_of_mem hp),same q (Finset.mem_insert_self ..)]
  · simpa [subRow,ip] using same i (Finset.mem_insert_of_mem hi)

theorem old_input_essential {s : Finset Coord} {f : Wire} (sup : supported s f)
    {p q v : Coord} (hp : p ∈ s) (fresh : q ∉ s) {o : Op} (binary : both o = true)
    (ess : essential f v) : essential (composeInput f o p q) v := by
  have pq : p ≠ q := fun e => fresh (e ▸ hp)
  obtain ⟨b,sg,back⟩ := left_section o binary
  obtain ⟨x,y,d,others⟩ := ess
  refine ⟨leftRow p q b sg x,leftRow p q b sg y,?_,?_⟩
  · simpa only [left_recovers sup pq fresh back] using d
  · intro i iv
    by_cases ip : i = p
    · subst i; simp [leftRow,others p iv]
    · simp [leftRow,ip,others i iv]

theorem new_input_essential {s : Finset Coord} {f : Wire} (sup : supported s f)
    {p q : Coord} (hp : p ∈ s) (fresh : q ∉ s) {o : Op} (binary : both o = true)
    (ess : essential f p) : essential (composeInput f o p q) q := by
  have pq : p ≠ q := fun e => fresh (e ▸ hp)
  obtain ⟨a,sg,back⟩ := right_section o binary
  obtain ⟨x,y,d,others⟩ := ess
  refine ⟨rightRow p q a sg x,rightRow p q a sg y,?_,?_⟩
  · simpa only [right_recovers sup pq fresh back] using d
  · intro i iq
    by_cases ip : i = p
    · subst i; simp [rightRow]
    · simp [rightRow,ip,iq,others i ip]

theorem left_image_input {p q : Coord} (pq : p ≠ q) (b sg : Bool) (j : Coord) :
    image (leftRow p q b sg) (input j) = if j = q then zero else input j := by
  by_cases jp : j = p
  · subst j; funext x; simp [image,normalize,leftRow,input,baseline,pq]
  · by_cases jq : j = q
    · subst j; funext x; simp [image,normalize,leftRow,input,zero,jp]
    · funext x; simp [image,normalize,leftRow,input,baseline,jp,jq]

theorem compose_lower (keys : List Coord) {f : Wire} (sup : supported keys.toFinset f)
    {p q : Coord} (hp : p ∈ keys) (hq : q ∉ keys) {o : Op} (binary : both o = true)
    (ess : essential f p) {k : ℕ} (h : native (q::keys) (composeInput f o p q) k) :
    ∃ l, l+1 ≤ k ∧ native keys f l := by
  have fresh : q ∉ keys.toFinset := by simpa using hq
  have pq : p ≠ q := fun e => hq (e ▸ hp)
  obtain ⟨b,sg,back⟩ := left_section o binary
  have target : image (leftRow p q b sg) (composeInput f o p q) = normalize f :=
    congrArg normalize (funext (left_recovers sup pq fresh back))
  have cover (j : Coord) (hj : j ∈ q::keys) :
      image (leftRow p q b sg) (input j) = zero ∨ image (leftRow p q b sg) (input j) ∈ primaryBank keys.toFinset := by
    rw [left_image_input pq]
    by_cases jq : j = q
    · simp [jq]
    · right
      rw [ite_eq_right jq]
      exact Finset.mem_image_of_mem _ (List.mem_toFinset.mpr ((List.mem_cons.mp hj).resolve_left jq))
  have gone (j : Coord) (hj : j ∈ ({q} : Finset Coord)) :
      essential (composeInput f o p q) j ∧ image (leftRow p q b sg) (input j) = zero := by
    obtain rfl := Finset.mem_singleton.mp hj
    exact ⟨new_input_essential sup (List.mem_toFinset.mpr hp) fresh binary ess,by simp [left_image_input pq]⟩
  simpa only [Finset.card_singleton] using
    project_native {q} target (nonzero_of_essential ess) cover gone h

def joinedOp (o : Op) (p q : Coord) := normalize (combine o (input p) (input q))

theorem subst_image_input (o : Op) (p q j : Coord) :
    image (subRow o p q) (input j) = if j = p then joinedOp o p q else input j := by
  by_cases eq : j = p
  · subst j; funext x; simp [image,normalize,subRow,input,joinedOp,combine]
  · funext x; simp [image,normalize,subRow,input,baseline,eq]

theorem compose_upper (keys : List Coord) {f : Wire} (sup : supported keys.toFinset f)
    {p q : Coord} (hp : p ∈ keys) (hq : q ∉ keys) {o : Op} (binary : both o = true)
    (ess : essential f p) {k : ℕ} (h : native keys f k) :
    native (q::keys) (composeInput f o p q) (k+1) := by
  have hp' := List.mem_toFinset.mpr hp
  have hq' : q ∉ keys.toFinset := by simpa using hq
  have nz := nonzero_of_essential (new_input_essential sup hp' hq' binary ess)
  have pg : image (subRow o p q) (normalize f) = normalize (composeInput f o p q) := normalize_twice ..
  have initial := (native_iff keys f k (nonzero_of_essential ess)).mp h
  obtain ⟨av,sub,lv⟩ := compress initial
  obtain ⟨l,bd,run⟩ := image_live (σ := subRow o p q) (pg ▸ nz) lv
  apply (native_iff _ _ _ nz).mpr
  unfold feasible
  rw [List.toFinset_cons,← pg]
  have ph : input p ∈ primaryBank (insert q keys.toFinset) := Finset.mem_image_of_mem _ (Finset.mem_insert_of_mem hp')
  have qh : input q ∈ primaryBank (insert q keys.toFinset) := Finset.mem_image_of_mem _ (Finset.mem_insert_self ..)
  have ne : input p ≠ input q := fun e => hq (input_injective e ▸ hp)
  have op : joinedOp o p q ∈ ops (input p) (input q) := by
    simpa only [joinedOp,input_normal] using normalized_op o (input p) (input q)
  apply Or.inr
  refine ⟨input p,ph,input q,qh,ne,joinedOp o p q,op,?_⟩
  apply steps (build_subset run ?_) (by omega)
  intro w hw
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hw).2
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp (sub ha)
  rw [subst_image_input]
  by_cases jp : j = p
  · simp [jp]
  · rw [ite_eq_right jp]
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_insert_of_mem hj))

theorem compose_iff (keys : List Coord) {f : Wire} (sup : supported keys.toFinset f)
    {p q : Coord} (hp : p ∈ keys) (hq : q ∉ keys) {o : Op} (binary : both o = true)
    (ess : essential f p) (k : ℕ) :
    native (q::keys) (composeInput f o p q) (k+1) ↔ native keys f k := by
  refine ⟨?_,compose_upper keys sup hp hq binary ess⟩
  intro h
  obtain ⟨l,bd,C,weight,ev⟩ := compose_lower keys sup hp hq binary ess h
  exact ⟨C,by omega,ev⟩

end
end Paired.Split
