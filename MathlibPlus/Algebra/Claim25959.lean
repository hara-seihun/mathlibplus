import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim25959

/-!
Formalization of the three displayed five-part power-sum identities in
admitted claim 25959.  The claim also mentions analogous complement
identities, but does not specify the complement convention; those are left
explicit for fidelity review rather than guessed here.
-/

/-- The three five-part power-sum identities in admitted claim 25959. -/
theorem powerSumIdentities_claim25959
    (μ₀ μ₁ μ₂ μ₃ μ₄ N : ℝ)
    (_hμ₀ : 0 ≤ μ₀) (_hμ₁ : 0 ≤ μ₁) (_hμ₂ : 0 ≤ μ₂)
    (_hμ₃ : 0 ≤ μ₃) (_hμ₄ : 0 ≤ μ₄)
    (hN : N = μ₀ + μ₁ + μ₂ + μ₃ + μ₄) :
    (μ₀ + μ₁) + (μ₀ + μ₂) + (μ₀ + μ₃) + (μ₀ + μ₄) +
        (μ₁ + μ₂) + (μ₁ + μ₃) + (μ₁ + μ₄) +
        (μ₂ + μ₃) + (μ₂ + μ₄) + (μ₃ + μ₄) = 4 * N ∧
      ((μ₀ + μ₁)^2 + (μ₀ + μ₂)^2 + (μ₀ + μ₃)^2 + (μ₀ + μ₄)^2 +
        (μ₁ + μ₂)^2 + (μ₁ + μ₃)^2 + (μ₁ + μ₄)^2 +
        (μ₂ + μ₃)^2 + (μ₂ + μ₄)^2 + (μ₃ + μ₄)^2 =
          3 * (μ₀^2 + μ₁^2 + μ₂^2 + μ₃^2 + μ₄^2) + N^2) ∧
      ((μ₀ + μ₁)^3 + (μ₀ + μ₂)^3 + (μ₀ + μ₃)^3 + (μ₀ + μ₄)^3 +
        (μ₁ + μ₂)^3 + (μ₁ + μ₃)^3 + (μ₁ + μ₄)^3 +
        (μ₂ + μ₃)^3 + (μ₂ + μ₄)^3 + (μ₃ + μ₄)^3 =
          μ₀^3 + μ₁^3 + μ₂^3 + μ₃^3 + μ₄^3 +
            3 * N * (μ₀^2 + μ₁^2 + μ₂^2 + μ₃^2 + μ₄^2)) := by
  constructor
  · rw [hN]
    ring
  constructor
  · rw [hN]
    ring
  · rw [hN]
    ring

end MathlibPlus.Algebra.Claim25959
