import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.RO0067Claim16478

noncomputable section

/-- Claim 16478: a fixed nonzero monic reciprocal integer polynomial has two
separate real roots outside the unit circle.  The witness is fixed in the
statement, so reciprocity cannot be witnessed by the zero polynomial or by an
unconstrained existential polynomial. -/
def reciprocalIntegerPolynomialCounterexample_claim16478 : Prop :=
  let P : Polynomial ℤ :=
    Polynomial.X ^ 4 - 7 * Polynomial.X ^ 3 +
      14 * Polynomial.X ^ 2 - 7 * Polynomial.X + 1
  let x : ℝ := (3 + Real.sqrt 5) / 2
  let y : ℝ := (4 + Real.sqrt 12) / 2
  P ≠ 0 ∧
    P.Monic ∧
    P.reverse = P ∧
    1 < x ∧
    1 < y ∧
    x ≠ y ∧
    Polynomial.eval₂ (Int.castRingHom ℝ) x P = 0 ∧
    Polynomial.eval₂ (Int.castRingHom ℝ) y P = 0 ∧
    Polynomial.eval₂ (Int.castRingHom ℝ) x⁻¹ P = 0 ∧
    Polynomial.eval₂ (Int.castRingHom ℝ) y⁻¹ P = 0

end

end MathlibPlus.Open.ResearchFormalization.RO0067Claim16478
