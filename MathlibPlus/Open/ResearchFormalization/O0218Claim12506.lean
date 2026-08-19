import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.O0218Claim12506

noncomputable section

open scoped BigOperators

/-- The factored prime-cyclic packet polynomial. -/
noncomputable def foldedPacketPolynomial (N : ℕ) : Polynomial ℝ :=
  (1 + Polynomial.X) *
    (1 + Polynomial.C (2 * Real.cos (2 * Real.pi / (N : ℝ))) *
      Polynomial.X + Polynomial.X ^ 2)

/-- Claim 12506: for N at least four, the factored packet expands to the
four displayed coefficients, all of which are strictly positive. -/
def claim12506 : Prop :=
  ∀ N : ℕ, 4 ≤ N →
    let θ : ℝ := 2 * Real.pi / (N : ℝ)
    let E : Polynomial ℝ := foldedPacketPolynomial N
    E =
        1 + Polynomial.C (1 + 2 * Real.cos θ) * Polynomial.X +
          Polynomial.C (1 + 2 * Real.cos θ) * Polynomial.X ^ 2 +
          Polynomial.X ^ 3 ∧
      0 < E.coeff 0 ∧
      0 < E.coeff 1 ∧
      0 < E.coeff 2 ∧
      0 < E.coeff 3

end
end MathlibPlus.Open.ResearchFormalization.O0218Claim12506
