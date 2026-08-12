import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace MathlibPlus.Analysis.Claim9639

/-- The two coordinate reflections preserve the symmetric rectangle and its
critical axis, commute, and are involutions.  This is the explicit
`C₂ × C₂` action recorded in claim 9639. -/
theorem symmetricRectangleAction
    (a b : ℝ) :
    let Q : Set (ℝ × ℝ) := {p | |p.1| ≤ a ∧ |p.2| ≤ b}
    let A : Set (ℝ × ℝ) := {p | p.1 = 0 ∧ |p.2| ≤ b}
    let σ : (ℝ × ℝ) → (ℝ × ℝ) := fun p => (-p.1, p.2)
    let τ : (ℝ × ℝ) → (ℝ × ℝ) := fun p => (p.1, -p.2)
    Function.Involutive σ ∧
      Function.Involutive τ ∧
      (∀ p, σ (τ p) = τ (σ p)) ∧
      (∃ p, σ p ≠ p) ∧
      (∃ p, τ p ≠ p) ∧
      (∃ p, σ p ≠ τ p) ∧
      Set.MapsTo σ Q Q ∧
      Set.MapsTo τ Q Q ∧
      Set.MapsTo σ A A ∧
      Set.MapsTo τ A A := by
  dsimp
  constructor
  · intro p
    rcases p with ⟨x, y⟩
    simp
  constructor
  · intro p
    rcases p with ⟨x, y⟩
    simp
  constructor
  · intro p
    rcases p with ⟨x, y⟩
    rfl
  constructor
  · refine ⟨(1, 0), ?_⟩
    norm_num
  constructor
  · refine ⟨(0, 1), ?_⟩
    norm_num
  constructor
  · refine ⟨(1, 0), ?_⟩
    norm_num
  constructor
  · intro p hp
    rcases p with ⟨x, y⟩
    rcases hp with ⟨hx, hy⟩
    exact ⟨by simpa [abs_neg] using hx, hy⟩
  constructor
  · intro p hp
    rcases p with ⟨x, y⟩
    rcases hp with ⟨hx, hy⟩
    exact ⟨hx, by simpa [abs_neg] using hy⟩
  constructor
  · intro p hp
    rcases p with ⟨x, y⟩
    rcases hp with ⟨hx, hy⟩
    exact ⟨by simpa [hx], hy⟩
  · intro p hp
    rcases p with ⟨x, y⟩
    rcases hp with ⟨hx, hy⟩
    exact ⟨hx, by simpa [abs_neg] using hy⟩

end MathlibPlus.Analysis.Claim9639
