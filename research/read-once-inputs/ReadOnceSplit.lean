import PairedCircuit

/-! Splitting an essential input into two fresh, disjoint inputs. -/
namespace Paired.Split
noncomputable section
open Classical LiveRestriction

def primaryBank (s : Finset Coord) : Finset Wire := s.image input
def feasible (s : Finset Coord) (f : Wire) (k : ℕ) := build ops (normalize f) k (primaryBank s)
def supported (s : Finset Coord) (f : Wire) := ∀ x y : Row, (∀ p ∈ s, x p = y p) → f x = f y
def essential (f : Wire) (p : Coord) := ∃ x y : Row, f x ≠ f y ∧ ∀ q ≠ p, x q = y q

def join (andGate a b : Bool) := if andGate then a && b else a || b
def subst (andGate : Bool) (p q : Coord) (x : Row) : Row :=
  Function.update x p (join andGate (x p) (x q))
def split (f : Wire) (andGate : Bool) (p q : Coord) : Wire := fun x => f (subst andGate p q x)
def pinVar (q : Coord) (b : Bool) (x : Row) : Row := Function.update x q b
def image (σ : Row → Row) (w : Wire) : Wire := normalize (fun x => w (σ x))

@[simp] theorem join_left (t b : Bool) : join t t b = b := by cases t <;> cases b <;> rfl
@[simp] theorem join_right (t a : Bool) : join t a t = a := by cases t <;> cases a <;> rfl
@[simp] theorem join_false (t : Bool) : join t false false = false := by cases t <;> rfl

theorem input_normal (p : Coord) : normalize (input p) = input p := by
  ext x
  simp [normalize,input,baseline]

theorem normalize_diff {f : Wire} {x y : Row} (h : f x ≠ f y) : normalize f x ≠ normalize f y := by
  cases f baseline <;> simp_all [normalize]

theorem nonzero_of_essential {f : Wire} {p : Coord} (h : essential f p) : normalize f ≠ zero := by
  obtain ⟨x,y,d,_⟩ := h
  intro eq
  have neq := normalize_diff d
  rw [eq] at neq
  exact neq rfl

theorem normalize_twice (σ : Row → Row) (f : Wire) : image σ (normalize f) = image σ f := by
  funext x
  simp only [image,normalize]
  cases f (σ x) <;> cases f (σ baseline) <;> cases f baseline <;> rfl

theorem image_preserves (σ : Row → Row) (a b z : Wire) (hz : z ∈ ops a b) :
    image σ z ∈ ops (image σ a) (image σ b) := by
  obtain ⟨o,_,rfl⟩ := ops_spec.mp hz
  exact normalized_op o (fun x => a (σ x)) (fun x => b (σ x))

theorem image_live {σ : Row → Row} {g : Wire} {k : ℕ} {av : Finset Wire}
    (nz : image σ g ≠ zero) (h : live ops g k av) :
    ∃ l, l + zeroCount (image σ) zero av ≤ k ∧
      build ops (image σ g) l (project (image σ) zero av) :=
  project_live ops ops (image σ) zero (fun a b z hz triv => op_simple (image_preserves σ a b z hz) triv)
    (image_preserves σ) nz h

theorem steps {g : Wire} {k l : ℕ} {av : Finset Wire} (h : build ops g k av) (le : k ≤ l) :
    build ops g l av := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le le
  clear le
  induction d with
  | zero => exact h
  | succ d ih => exact Or.inl ih

theorem support_split {s : Finset Coord} {f : Wire} (sup : supported s f)
    {p q : Coord} (hp : p ∈ s) (t : Bool) : supported (insert q s) (split f t p q) := by
  intro x y eq
  apply sup
  intro v hv
  by_cases vp : v = p
  · subst v
    simp [subst,eq p (Finset.mem_insert_of_mem hp),eq q (Finset.mem_insert_self ..)]
  · simpa [subst,vp] using eq v (Finset.mem_insert_of_mem hv)

theorem pinned_split {s : Finset Coord} {f : Wire} (sup : supported s f) {p q : Coord}
    (fresh : q ∉ s) (t : Bool) (x : Row) : split f t p q (pinVar q t x) = f x := by
  apply sup
  intro v hv
  have vq : v ≠ q := fun e => fresh (e ▸ hv)
  by_cases vp : v = p
  · subst v; simp [subst,pinVar,vq]
  · simp [subst,pinVar,vp,vq]

theorem preserve_essential {s : Finset Coord} {f : Wire} (sup : supported s f)
    {p q v : Coord} (fresh : q ∉ s) (t : Bool) (h : essential f v) :
    essential (split f t p q) v := by
  obtain ⟨x,y,d,out⟩ := h
  refine ⟨pinVar q t x,pinVar q t y,?_,?_⟩
  · simpa only [pinned_split sup fresh] using d
  · intro i ne
    by_cases iq : i = q
    · simp [pinVar,iq]
    · simp [pinVar,iq,out i ne]

theorem fresh_essential {s : Finset Coord} {f : Wire} (sup : supported s f) {p q : Coord}
    (hp : p ∈ s) (fresh : q ∉ s) (t : Bool) (h : essential f p) : essential (split f t p q) q := by
  have pq : p ≠ q := fun e => fresh (e ▸ hp)
  let lift (x : Row) := Function.update (Function.update x p t) q (x p)
  have recover (x : Row) : split f t p q (lift x) = f x := by
    apply sup
    intro v hv
    have vq : v ≠ q := fun e => fresh (e ▸ hv)
    by_cases vp : v = p
    · subst v; simp [subst,lift,pq]
    · simp [subst,lift,vp,vq]
  obtain ⟨x,y,d,out⟩ := h
  refine ⟨lift x,lift y,by simpa only [recover] using d,?_⟩
  intro v vq
  by_cases vp : v = p
  · simp [lift,vp,pq]
  · simp [lift,vq,vp,out v vp]

theorem pinned_input (q : Coord) (t : Bool) (p : Coord) :
    image (pinVar q t) (input p) = if p = q then zero else input p := by
  by_cases eq : p = q
  · subst p; ext x; simp [image,pinVar,input,normalize,zero]
  · ext x; simp [image,pinVar,input,normalize,baseline,eq]

theorem split_lower {s : Finset Coord} {f : Wire} (sup : supported s f) {p q : Coord}
    (hp : p ∈ s) (fresh : q ∉ s) (t : Bool) (ess : essential f p) {k : ℕ}
    (h : feasible (insert q s) (split f t p q) k) :
    ∃ l, l + 1 ≤ k ∧ feasible s f l := by
  let σ := pinVar q t
  let goal := normalize (split f t p q)
  have im : image σ goal = normalize f := by
    rw [show goal = normalize (split f t p q) from rfl,normalize_twice]
    apply congrArg normalize
    exact funext (pinned_split sup fresh t)
  have nz : image σ goal ≠ zero := im ▸ nonzero_of_essential ess
  obtain ⟨av,sub,lv⟩ := compress h
  obtain ⟨l,bd,run⟩ := image_live (σ := σ) nz lv
  obtain ⟨x,y,diff,out⟩ := fresh_essential sup hp fresh t ess
  obtain ⟨a,ha,neq⟩ := live_distinguishes lv x y (normalize_diff diff)
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp (sub ha)
  have iq : i = q := by by_contra no; exact neq (out i no)
  have iz : image σ (input i) = zero := by simp [σ,pinned_input,iq]
  have paid : 1 ≤ zeroCount (image σ) zero av :=
    Finset.card_pos.mpr ⟨input i,Finset.mem_filter.mpr ⟨ha,iz⟩⟩
  refine ⟨l,by omega,?_⟩
  unfold feasible
  rw [← im]
  apply build_subset run
  intro w hw
  obtain ⟨nz',mem⟩ := Finset.mem_erase.mp hw
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp mem
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp (sub hv)
  have jq : j ≠ q := by rintro rfl; exact nz' (by simp [σ,pinned_input])
  rw [show image σ (input j) = input j by simp [σ,pinned_input,jq]]
  exact Finset.mem_image_of_mem _ ((Finset.mem_insert.mp hj).resolve_left jq)

def joined (t : Bool) (p q : Coord) : Wire := fun x => join t (x p) (x q)

theorem joined_mem (t : Bool) (p q : Coord) : joined t p q ∈ ops (input p) (input q) :=
  ops_spec.mpr ⟨join t,join_false t,rfl⟩

theorem subst_input (t : Bool) (p q v : Coord) :
    image (subst t p q) (input v) = if v = p then joined t p q else input v := by
  by_cases eq : v = p
  · subst v; ext x; simp [image,subst,normalize,input,baseline,joined]
  · ext x; simp [image,subst,normalize,input,baseline,eq]

theorem split_upper {s : Finset Coord} {f : Wire} (sup : supported s f) {p q : Coord}
    (hp : p ∈ s) (fresh : q ∉ s) (t : Bool) (ess : essential f p) {k : ℕ}
    (h : feasible s f k) : feasible (insert q s) (split f t p q) (k+1) := by
  let σ := subst t p q
  have pg : image σ (normalize f) = normalize (split f t p q) := normalize_twice σ f
  have nz : image σ (normalize f) ≠ zero := pg ▸ nonzero_of_essential (fresh_essential sup hp fresh t ess)
  obtain ⟨av,sub,lv⟩ := compress h
  obtain ⟨l,bound,run⟩ := image_live nz lv
  have pbank : input p ∈ primaryBank (insert q s) := Finset.mem_image_of_mem _ (Finset.mem_insert_of_mem hp)
  have qbank : input q ∈ primaryBank (insert q s) := Finset.mem_image_of_mem _ (Finset.mem_insert_self ..)
  have pq : input p ≠ input q := fun e => fresh (input_injective e ▸ hp)
  apply Or.inr
  refine ⟨input p,pbank,input q,qbank,pq,joined t p q,joined_mem ..,?_⟩
  rw [← pg]
  apply steps (build_subset run ?_) (by omega)
  intro w hw
  obtain ⟨_,mem⟩ := Finset.mem_erase.mp hw
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp mem
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp (sub hv)
  by_cases eq : j = p
  · simp [σ,subst_input,eq]
  · rw [show image σ (input j) = input j by simp [σ,subst_input,eq]]
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_insert_of_mem hj))

theorem split_iff {s : Finset Coord} {f : Wire} (sup : supported s f) {p q : Coord}
    (hp : p ∈ s) (fresh : q ∉ s) (t : Bool) (ess : essential f p) (k : ℕ) :
    feasible (insert q s) (split f t p q) (k+1) ↔ feasible s f k := by
  refine ⟨?_,split_upper sup hp fresh t ess⟩
  intro h
  obtain ⟨l,bd,run⟩ := split_lower sup hp fresh t ess h
  exact steps run (by omega)

end
end Paired.Split
