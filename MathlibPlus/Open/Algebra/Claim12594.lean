import MathlibPlus.Basic

open scoped BigOperators

namespace MathlibPlus.Open.Algebra.Claim12594

/-- The coefficient `ℓ¹` norm used by the bounded-node product estimate. -/
private noncomputable def coeffL1 (p : Polynomial ℂ) : ℝ :=
  ∑ k ∈ p.support, ‖p.coeff k‖

/--
A formal registry statement of the bounded-node product estimate.  The source's
`deg S` is represented by `S.natDegree`; the coefficient norm is the finite
sum of the norms of the coefficients.  The parameter nonnegativity is made
explicit so that the displayed upper bound has its intended order meaning.
-/
noncomputable def boundedNodeProductL1Estimate : Prop :=
  ∀ (N : ℕ) (S : Polynomial ℂ) (A R : ℝ) (ρ : Fin N → ℂ),
    let D := N + S.natDegree
    0 ≤ A →
    0 ≤ R →
    D ≥ 1 →
    (∀ j, ‖ρ j‖ ≤ R) →
    coeffL1 S ≤ A ^ D →
    let W := S * ∏ j : Fin N, (Polynomial.X - Polynomial.C (ρ j))
    coeffL1 W ≤ coeffL1 S * ∏ j : Fin N, (1 + ‖ρ j‖) ∧
      coeffL1 S * ∏ j : Fin N, (1 + ‖ρ j‖) ≤ (A * (1 + R)) ^ D ∧
      ∀ k, ‖W.coeff k‖ ≤ (A * (1 + R)) ^ D

end MathlibPlus.Open.Algebra.Claim12594
