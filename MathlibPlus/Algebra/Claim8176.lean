import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim8176

/-!
The source calls the coefficient condition `PF₂`.  Since no local definition
of that name is supplied, its exact adjacent log-concavity consequence is
used directly here.
-/

/-- Positive coefficient log-concavity is equivalent to adjacent ratio decrease. -/
theorem positiveCoefficientRatioDecrease_claim8176
    (f : ℕ → ℝ) (hpos : ∀ n, 0 < f n)
    (hpf : ∀ n, f (n + 1)^2 ≥ f n * f (n + 2)) :
    ∀ n, f (n + 2) / f (n + 1) ≤ f (n + 1) / f n := by
  intro n
  rw [div_le_div_iff₀ (hpos (n + 1)) (hpos n)]
  nlinarith [hpf n]

end MathlibPlus.Algebra.Claim8176
