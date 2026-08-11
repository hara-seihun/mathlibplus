import Mathlib

namespace MathlibPlus.Algebra.Claim33646

/--
The displayed terminal-anchor reconstruction identities are exact algebraic
consequences of the two equations in claim 33646.  The marked-row and rooted
occurrence-count carriers are left as explicit rational parameters.
-/
theorem terminalAnchorReconstruction_claim33646
    (L q₁ q₂ q d₄ : ℚ)
    (hq : q = q₁ + q₂)
    (hd₄ : d₄ = q₁ * (L - 1) + q₂ * (L - 2)) :
    q = q₁ + q₂ ∧
      q₁ = d₄ - (L - 2) * q ∧
      q₂ = (L - 1) * q - d₄ := by
  refine ⟨hq, ?_, ?_⟩
  · calc
      q₁ = q₁ * (L - 1) + q₂ * (L - 2) - (L - 2) * (q₁ + q₂) := by ring
      _ = d₄ - (L - 2) * q := by rw [hd₄, hq]
  · calc
      q₂ = (L - 1) * (q₁ + q₂) -
          (q₁ * (L - 1) + q₂ * (L - 2)) := by ring
      _ = (L - 1) * q - d₄ := by rw [hd₄, hq]

end MathlibPlus.Algebra.Claim33646
