import Mathlib

open scoped BigOperators

/-!
# Linear degree-offset coefficient envelope

Statement-fidelity formalization of admitted claim 3066. The source's `B(P)`
coefficient-root envelope is expanded into its coefficient inequalities, so no
unstated convention for the degree-zero term or the ambient coefficient field
is introduced.
-/

namespace MathlibPlus.Open.Analysis

/-- Exponential coefficient control for a polynomial block shifted by a degree
`q` that is linearly comparable to the total unshifted degree. -/
def linearDegreeOffsetCoefficientEnvelope_claim3066 : Prop :=
  ∀ (A R δ Γ : ℝ) (N q : ℕ) (S : Polynomial ℂ)
      (ρ : Fin N → ℂ),
    1 ≤ A →
    0 ≤ R →
    0 < δ →
    δ ≤ Γ →
    let D : ℕ := N + S.natDegree
    let Δ : Polynomial ℂ :=
      Polynomial.monomial q (1 : ℂ) * S *
        ∏ j : Fin N, (Polynomial.X - Polynomial.C (ρ j))
    1 ≤ D →
    (∀ j : Fin N, ‖ρ j‖ ≤ R) →
    (∑ n ∈ S.support, ‖S.coeff n‖) ≤ A ^ D →
    δ * (D : ℝ) ≤ (q : ℝ) →
    (q : ℝ) ≤ Γ * (D : ℝ) →
    (∀ n : ℕ, 1 ≤ n →
      Real.rpow ‖(1 + Δ).coeff n‖ (1 / (n : ℝ)) ≤
        max 1 (Real.rpow (A * (1 + R)) (1 / δ))) ∧
      ((Polynomial.natDegree (1 + Δ) : ℕ) : ℝ) ≤
        (Γ + 1) * (D : ℝ)

end MathlibPlus.Open.Analysis
