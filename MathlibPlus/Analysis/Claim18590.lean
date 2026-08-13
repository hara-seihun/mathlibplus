import MathlibPlus.Basic

namespace MathlibPlus.Analysis.Claim18590

/-!
The packet does not define the determinant `W` or the separated-chamber
parameters beyond the displayed factorization.  The factorization is kept as
an explicit hypothesis, while its exact positive-factor consequence is
kernel-checked below.
-/

/-- The positive-factor reduction of the rank-three determinant in claim 18590. -/
theorem exactScalarFactorization_claim18590
    (ℓ q₁ q₂ q₃ P h₂ N W : ℝ)
    (hℓ : 0 < ℓ) (_hP : 0 < P) (hN : 0 < N)
    (hW : W = ℓ ^ (-15 / 4 : ℝ) * Real.exp (-(q₁ + q₂ + q₃) / ℓ) * (P - h₂ * N)) :
    W > 0 ↔ h₂ < P / N := by
  have hfac : 0 < ℓ ^ (-15 / 4 : ℝ) * Real.exp (-(q₁ + q₂ + q₃) / ℓ) := by
    positivity
  constructor
  · intro hWpos
    rw [hW] at hWpos
    have hdiff : 0 < P - h₂ * N :=
      pos_of_mul_pos_right hWpos (le_of_lt hfac)
    exact (lt_div_iff₀ hN).2 (by nlinarith)
  · intro hh
    have hdiff : 0 < P - h₂ * N := by
      have hmul : h₂ * N < P := (lt_div_iff₀ hN).1 hh
      nlinarith
    rw [hW]
    exact mul_pos hfac hdiff

end MathlibPlus.Analysis.Claim18590
