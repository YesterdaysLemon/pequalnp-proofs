import FirstGateBasis
import ReadOnceBinary

namespace FirstGate
open Paired Paired.Split LiveRestriction PEqualNP.MetaComplexity
noncomputable section
open Classical

def bounded (all : Bool) (keys : List Coord) (f : Wire) (k : Nat) :=
  build (family all) (normalize f) k (primaryBank keys.toFinset)

theorem image_family {all : Bool} (σ : Row → Row) {a b z : Wire} (hz : z ∈ family all a b) :
    image σ z ∈ family all (image σ a) (image σ b) := by
  obtain ⟨o,⟨_,allowed⟩,rfl⟩ := member.mp hz
  exact normalize_member o allowed (fun x => a (σ x)) (fun x => b (σ x))

theorem project_one {all : Bool} {f g : Wire} {before after : List Coord} {q : Coord}
    (σ : Row → Row) (target : image σ f = normalize g) (nz : normalize g ≠ zero)
    (cover : ∀ p ∈ before, image σ (input p) = zero ∨ image σ (input p) ∈ primaryBank after.toFinset)
    (ess : essential f q) (gone : image σ (input q) = zero) {k : Nat} (run : bounded all before f k) :
    ∃ l, l+1 ≤ k ∧ bounded all after g l := by
  have out : image σ (normalize f) = normalize g := (normalize_twice ..).trans target
  obtain ⟨s,sub,lv⟩ := compress run
  obtain ⟨x,y,d,others⟩ := ess
  obtain ⟨w,hw,dw⟩ := live_distinguishes (relax lv) x y (normalize_diff d)
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp (sub hw)
  have iq : i = q := by by_contra ne; exact dw (others i ne)
  have count : 0 < zeroCount (image σ) zero s := Finset.card_pos.mpr
    ⟨input i,Finset.mem_filter.mpr ⟨hw,iq ▸ gone⟩⟩
  obtain ⟨l,bd,smaller⟩ := project_live (family all) (family all) (image σ) zero
    (fun _ _ _ m e => op_simple (included (image_family σ m)) e)
    (fun _ _ _ m => image_family σ m) (out ▸ nz) lv
  refine ⟨l,by omega,?_⟩
  unfold bounded
  rw [← out]
  apply build_subset smaller
  intro w hw
  obtain ⟨ne,pack⟩ := Finset.mem_erase.mp hw
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp pack
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp (sub hv)
  exact (cover p (List.mem_toFinset.mp hp)).resolve_left ne

theorem substitution_lower {all : Bool} (keys : List Coord) {f : Wire} (sup : supported keys.toFinset f)
    {p q : Coord} (hp : p ∈ keys) (hq : q ∉ keys) {o : Op} (uses : both o = true)
    (ess : essential f p) {k : Nat} (run : bounded all (q::keys) (composeInput f o p q) k) :
    ∃ l, l+1 ≤ k ∧ bounded all keys f l := by
  have fresh : q ∉ keys.toFinset := by simpa using hq
  have pq : p ≠ q := fun e => hq (e ▸ hp)
  obtain ⟨b,sg,back⟩ := left_section o uses
  apply project_one (q := q) (leftRow p q b sg) _ (nonzero_of_essential ess) _ _ _ run
  · exact congrArg normalize (funext (left_recovers sup pq fresh back))
  · intro i hi
    rw [left_image_input pq]
    by_cases iq : i = q
    · simp [iq]
    · right
      rw [ite_eq_right iq]
      exact Finset.mem_image_of_mem _ (List.mem_toFinset.mpr ((List.mem_cons.mp hi).resolve_left iq))
  · exact new_input_essential sup (List.mem_toFinset.mpr hp) fresh uses ess
  · simp [left_image_input pq]

theorem refined_lower {all : Bool} {start base keys f d} (r : Refined start base keys f d)
    (sup : supported start.toFinset base) (used : ∀ p ∈ start, essential base p)
    {c : Nat} (low : ∀ k, bounded all start base k → c ≤ k) (k : Nat) (run : bounded all keys f k) :
    c+d ≤ k := by
  induction r generalizing k with
  | start => exact low k run
  | @extend old g _ p q prior hp hq o binary ih =>
    obtain ⟨valid,ess⟩ := refined_inputs prior sup used
    obtain ⟨l,spare,projected⟩ := substitution_lower old valid hp hq binary (ess _ hp) run
    have smaller := ih l projected
    omega

end
end FirstGate
