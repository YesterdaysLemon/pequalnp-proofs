import SplitCircuits

namespace Paired.Split
noncomputable section
open Classical LiveRestriction

-- A projection may pin, complement, identify or rename the other inputs.
theorem project_native {keys kept : List Coord} {f g : Wire} {σ : Row → Row}
    (fixed : Finset Coord) (target : image σ f = normalize g) (nz : normalize g ≠ zero)
    (cover : ∀ p ∈ keys, image σ (input p) = zero ∨ image σ (input p) ∈ primaryBank kept.toFinset)
    (gone : ∀ p ∈ fixed, essential f p ∧ image σ (input p) = zero)
    {k : ℕ} (h : native keys f k) : ∃ l, l + fixed.card ≤ k ∧ native kept g l := by
  have projected : image σ (normalize f) = normalize g := (normalize_twice ..).trans target
  have nz' : image σ (normalize f) ≠ zero := projected ▸ nz
  have original : normalize f ≠ zero := by
    intro e
    apply nz'
    rw [e]
    funext x
    simp [image,normalize,zero]
  obtain ⟨s,sub,lv⟩ := compress ((native_iff keys f k original).mp h)
  have lost : fixed.image input ⊆ s.filter (fun a => image σ a = zero) := by
    intro a ha
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨ess,pinned⟩ := gone p hp
    obtain ⟨x,y,diff,others⟩ := ess
    obtain ⟨v,hv,neq⟩ := live_distinguishes lv x y (normalize_diff diff)
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp (sub hv)
    have eq : j = p := by by_contra ne; exact neq (others j ne)
    exact Finset.mem_filter.mpr ⟨eq ▸ hv,pinned⟩
  have paid := Finset.card_le_card lost
  rw [Finset.card_image_of_injective _ input_injective] at paid
  change fixed.card ≤ zeroCount (image σ) zero s at paid
  obtain ⟨l,bd,run⟩ := image_live nz' lv
  refine ⟨l,by omega,(native_iff kept g l nz).mpr ?_⟩
  unfold feasible
  rw [← projected]
  apply build_subset run
  intro w hw
  obtain ⟨notZero,mem⟩ := Finset.mem_erase.mp hw
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp mem
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp (sub hv)
  exact (cover p (List.mem_toFinset.mp hp)).resolve_left notZero

def pin (fixed : Finset Coord) (bits : Coord → Bool) (x : Row) : Row :=
  fun p => if p ∈ fixed then bits p else x p

theorem pin_input (fixed : Finset Coord) (bits : Coord → Bool) (p : Coord) :
    image (pin fixed bits) (input p) = if p ∈ fixed then zero else input p := by
  by_cases hp : p ∈ fixed
  · funext x; simp [image,pin,normalize,input,zero,hp]
  · funext x; simp [image,pin,normalize,input,baseline,hp]

theorem restrict_native {keys : List Coord} {f : Wire} (fixed : Finset Coord)
    (bits : Coord → Bool) (used : ∀ p ∈ fixed, essential f p)
    (nz : normalize (f ∘ pin fixed bits) ≠ zero) {k : ℕ} (h : native keys f k) :
    ∃ l, l + fixed.card ≤ k ∧ native (keys.filter (fun p => p ∉ fixed)) (f ∘ pin fixed bits) l := by
  apply project_native (f := f) (σ := pin fixed bits) fixed rfl nz _ _ h
  · intro p hp
    rw [pin_input]
    by_cases mem : p ∈ fixed
    · simp [mem]
    · right
      rw [ite_eq_right mem]
      apply Finset.mem_image_of_mem
      exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hp,by simp [mem]⟩)
  · intro p hp
    exact ⟨used p hp,by simp [pin_input,hp]⟩

end
end Paired.Split
