import CycleCircuit
import EssentialRestrictions

namespace CycleCircuit
noncomputable section
open Paired Paired.Split

def adjacent (i j : Fin 5) : Prop := (i.val+1)%5 = j.val ∨ (j.val+1)%5 = i.val

theorem spec_true (x : Fin 5 → Bool) : spec x = true ↔ ∃ i j, adjacent i j ∧ x i = true ∧ x j = true := by
  revert x
  unfold adjacent
  decide +kernel

open Classical

def edgeFn (edges : Finset (Coord × Coord)) (x : Row) : Bool :=
  decide (∃ e ∈ edges, x e.1 = true ∧ x e.2 = true)

def undirected (edges : Finset (Coord × Coord)) (p q : Coord) : Prop := (p,q) ∈ edges ∨ (q,p) ∈ edges

theorem edge_true (edges : Finset (Coord × Coord)) (x : Row) :
    edgeFn edges x = true ↔ ∃ p q, undirected edges p q ∧ x p = true ∧ x q = true := by
  simp only [edgeFn,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨p,q⟩,hm,hp,hq⟩
    exact ⟨p,q,.inl hm,hp,hq⟩
  · rintro ⟨p,q,h,hp,hq⟩
    rcases h with f | r
    · exact ⟨(p,q),f,hp,hq⟩
    · exact ⟨(q,p),r,hq,hp⟩

def route (e : Fin 5 → Coord) (x : Row) (p : Coord) : Bool :=
  decide (∃ i, e i = p ∧ x (coord i) = true)

theorem route_at {e : Fin 5 → Coord} (inj : Function.Injective e) (x : Row) (i : Fin 5) :
    route e x (e i) = x (coord i) := by
  apply Bool.eq_iff_iff.mpr
  simp only [route,decide_eq_true_eq]
  constructor
  · rintro ⟨j,eq,yes⟩
    exact inj eq ▸ yes
  · exact fun yes => ⟨i,rfl,yes⟩

theorem route_none {e : Fin 5 → Coord} {p : Coord} (out : ∀ i, e i ≠ p) (x : Row) :
    route e x p = false := by
  simp [route,out]

theorem induced_eval {edges : Finset (Coord × Coord)} (e : Fin 5 → Coord) (inj : Function.Injective e)
    (induced : ∀ i j, undirected edges (e i) (e j) ↔ adjacent i j) (x : Row) :
    edgeFn edges (route e x) = fn x := by
  apply Bool.eq_iff_iff.mpr
  rw [edge_true,fn,spec_true]
  constructor
  · rintro ⟨p,q,edge,hp,hq⟩
    obtain ⟨i,rfl,yes⟩ := of_decide_eq_true hp
    obtain ⟨j,rfl,also⟩ := of_decide_eq_true hq
    exact ⟨i,j,(induced i j).mp edge,yes,also⟩
  · rintro ⟨i,j,edge,yes,also⟩
    exact ⟨e i,e j,(induced i j).mpr edge,(route_at inj x i).trans yes,(route_at inj x j).trans also⟩

theorem simple_essential {edges : Finset (Coord × Coord)} {p q : Coord}
    (neighbor : undirected edges p q) (noLoop : (q,q) ∉ edges) : essential (edgeFn edges) p := by
  let single : Row := fun v => decide (v = q)
  let pair : Row := fun v => decide (v = p ∨ v = q)
  have no : edgeFn edges single = false := by
    apply Bool.eq_false_iff.mpr
    intro yes
    obtain ⟨a,b,edge,ha,hb⟩ := (edge_true edges single).mp yes
    have aq : a = q := of_decide_eq_true ha
    have bq : b = q := of_decide_eq_true hb
    rcases aq with rfl
    rcases bq with rfl
    exact noLoop (edge.elim id id)
  have yes : edgeFn edges pair = true :=
    (edge_true edges pair).mpr ⟨p,q,neighbor,by simp [pair],by simp [pair]⟩
  refine ⟨single,pair,by simp [no,yes],?_⟩
  intro v vp
  simp [single,pair,vp]

theorem projected_input {e : Fin 5 → Coord} (inj : Function.Injective e) (p : Coord) :
    image (route e) (input p) = zero ∨ image (route e) (input p) ∈ primaryBank keys.toFinset := by
  by_cases mem : ∃ i, e i = p
  · obtain ⟨i,rfl⟩ := mem
    right
    have eq : image (route e) (input (e i)) = input (coord i) := by
      funext x; simp [image,input,normalize,route_at inj,baseline]
    rw [eq]
    exact Finset.mem_image_of_mem _ (List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨i,rfl⟩))
  · left
    have absent : ∀ i, e i ≠ p := fun i eq => mem ⟨i,eq⟩
    funext x; simp [image,input,normalize,route_none absent,zero]

theorem induced_lower {edges : Finset (Coord × Coord)} {inputs : List Coord} {k : ℕ}
    (e : Fin 5 → Coord) (inj : Function.Injective e)
    (induced : ∀ i j, undirected edges (e i) (e j) ↔ adjacent i j)
    (others : Finset Coord) (out : ∀ p ∈ others, ∀ i, e i ≠ p)
    (essentialOthers : ∀ p ∈ others, essential (edgeFn edges) p)
    (h : native inputs (edgeFn edges) k) : 7 + others.card ≤ k := by
  have target : image (route e) (edgeFn edges) = normalize fn :=
    congrArg normalize (funext (induced_eval e inj induced))
  obtain ⟨l,bd,run⟩ := project_native (kept := keys) others target nonzero (fun p _ => projected_input inj p)
    (fun p hp => ⟨essentialOthers p hp,by funext x; simp [image,normalize,input,route_none (out p hp),zero]⟩) h
  have lb := lower run
  omega

theorem graph_size_lower {edges : Finset (Coord × Coord)} {inputs : List Coord} {k : ℕ}
    (nd : inputs.Nodup) (loopless : ∀ p, (p,p) ∉ edges)
    (incident : ∀ p ∈ inputs, ∃ q, undirected edges p q)
    (e : Fin 5 → Coord) (inj : Function.Injective e) (present : ∀ i, e i ∈ inputs)
    (induced : ∀ i j, undirected edges (e i) (e j) ↔ adjacent i j)
    (h : native inputs (edgeFn edges) k) : inputs.length + 2 ≤ k := by
  let vertices := Finset.univ.image e
  let others := inputs.toFinset \ vertices
  have card : vertices.card = 5 := by
    simp [vertices,Finset.card_image_of_injective _ inj]
  have subset : vertices ⊆ inputs.toFinset := by
    intro p hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    exact List.mem_toFinset.mpr (present i)
  have count := Finset.card_sdiff_of_subset subset
  have all := List.toFinset_card_of_nodup nd
  have outside (p : Coord) (hp : p ∈ others) (i : Fin 5) : e i ≠ p := by
    rintro rfl
    exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have needed (p : Coord) (hp : p ∈ others) : essential (edgeFn edges) p := by
    obtain ⟨q,edge⟩ := incident p (List.mem_toFinset.mp (Finset.mem_sdiff.mp hp).1)
    exact simple_essential edge (loopless q)
  have bound := induced_lower e inj induced others outside needed h
  change 7 + (inputs.toFinset \ vertices).card ≤ k at bound
  omega

end
end CycleCircuit
