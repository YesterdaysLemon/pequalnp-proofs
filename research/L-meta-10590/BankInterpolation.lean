import PEqualNP.Defs

namespace BankInterpolation

variable {α : Type*} [Preorder α]

-- Each element of the preorder is a vector of live wire values.
-- P and N are the images of the positive and negative assignments.
def badP (P N : Set α) (p : α) : Prop := p ∈ P ∧ ∃ n ∈ N, p ≤ n
def badN (P N : Set α) (n : α) : Prop := n ∈ N ∧ ∃ p ∈ P, p ≤ n

theorem monotoneTail (P N : Set α) :
    (∃ h : α → Prop, Monotone h ∧ (∀ p ∈ P, h p) ∧ (∀ n ∈ N, ¬ h n)) ↔
    ∀ p ∈ P, ∀ n ∈ N, ¬ p ≤ n := by
  constructor
  · rintro ⟨h, hm, hp, hn⟩ p hP n hN hpn
    exact hn n hN (hm hpn (hp p hP))
  · intro sep
    refine ⟨fun u => ∃ p ∈ P, p ≤ u, ?_, ?_, ?_⟩
    · rintro u v huv ⟨p, hP, hpu⟩
      exact ⟨p, hP, hpu.trans huv⟩
    · exact fun p hP => ⟨p, hP, le_rfl⟩
    · rintro n hN ⟨p, hP, hpn⟩
      exact sep p hP n hN hpn

theorem oneNegation (P N : Set α) :
    (∃ g : α → Prop, Monotone g ∧ ∃ h : α × Prop → Prop, Monotone h ∧
      (∀ p ∈ P, h (p, ¬ g p)) ∧ (∀ n ∈ N, ¬ h (n, ¬ g n))) ↔
    ∀ n p, badN P N n → badP P N p → ¬ n ≤ p := by
  classical
  constructor
  · rintro ⟨g, gm, h, hm, hp, hn⟩
    have cross : ∀ p ∈ P, ∀ n ∈ N, p ≤ n → ¬ g p ∧ g n := by
      intro p hP n hN hpn
      have no : ¬ ((¬ g p) → (¬ g n)) := by
        intro cond
        exact hn n hN (hm (show (p, ¬ g p) ≤ (n, ¬ g n) from ⟨hpn, cond⟩) (hp p hP))
      tauto
    rintro n p ⟨hN, q, hQ, hqn⟩ ⟨hP, r, hR, hpr⟩ hnp
    exact (cross p hP r hR hpr).1 (gm hnp (cross q hQ n hN hqn).2)
  · intro sep
    let g (u : α) : Prop := ∃ n, badN P N n ∧ n ≤ u
    have gm : Monotone g := by
      rintro u v huv ⟨n, hN, hnu⟩
      exact ⟨n, hN, hnu.trans huv⟩
    let h (v : α × Prop) : Prop := ∃ p ∈ P, (p, ¬ g p) ≤ v
    refine ⟨g, gm, h, ?_, ?_, ?_⟩
    · rintro u v huv ⟨p, hP, hpu⟩
      exact ⟨p, hP, hpu.trans huv⟩
    · exact fun p hP => ⟨p, hP, le_rfl⟩
    · rintro n hN ⟨p, hP, hpn⟩
      have bN : badN P N n := ⟨hN, p, hP, hpn.1⟩
      have bP : badP P N p := ⟨hP, n, hN, hpn.1⟩
      have hgp : ¬ g p := by
        rintro ⟨q, bQ, hqp⟩
        exact sep q p bQ bP hqp
      exact hpn.2 hgp ⟨n, bN, le_rfl⟩

end BankInterpolation
