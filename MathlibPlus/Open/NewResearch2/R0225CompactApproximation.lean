import Mathlib
import MathlibPlus.Analysis.ReciprocalXi

namespace MathlibPlus.Open.NewResearch2.R0225CompactApproximation

noncomputable section

/-- The closed rational rectangle used for compact-open approximation. -/
def rationalRectangleClosed (a b c d : ℚ) : Set ℂ :=
  {z : ℂ |
    (a : ℝ) ≤ z.re ∧ z.re ≤ (b : ℝ) ∧
      (c : ℝ) ≤ z.im ∧ z.im ≤ (d : ℝ)}

/-- The boundary of the closed rational rectangle. -/
def rationalRectangleBoundary (a b c d : ℚ) : Set ℂ :=
  rationalRectangleClosed a b c d \
    {z : ℂ |
      (a : ℝ) < z.re ∧ z.re < (b : ℝ) ∧
        (c : ℝ) < z.im ∧ z.im < (d : ℝ)}

/-- A finite rational coefficient list interpreted as a rational polynomial. -/
def rationalPolynomial (coefficients : List ℚ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range coefficients.length,
    Polynomial.C (coefficients.getD i 0) * Polynomial.X ^ i

/-- Claim 18986: the centered entire function `X(z)=ξ(1/2+z)` has an
 effective rational-polynomial approximation on every compact rational
 rectangle, and any strict boundary margin larger than the rational error
 tolerance yields the strict Rouché comparison on that boundary. -/
def claim18986 : Prop :=
  let X : ℂ → ℂ := MathlibPlus.Analysis.ReciprocalXi.centeredXi
  ∃ approximation : (ℚ × ℚ × ℚ × ℚ × ℚ) → List ℚ,
    Computable approximation ∧
      (∀ (a b c d ε : ℚ),
        a < b → c < d → 0 < ε →
          ∀ z : ℂ, rationalRectangleClosed a b c d z →
            ‖X z -
                Polynomial.eval z
                  ((rationalPolynomial
                    (approximation (a, b, c, d, ε))).map
                    (algebraMap ℚ ℂ))‖ < (ε : ℝ)) ∧
      (∀ (a b c d ε δ : ℚ),
        a < b → c < d → 0 < ε → 0 < δ → ε < δ →
          (∀ z : ℂ, rationalRectangleBoundary a b c d z →
            (δ : ℝ) ≤ ‖X z‖) →
          ∀ z : ℂ, rationalRectangleBoundary a b c d z →
            ‖X z -
                Polynomial.eval z
                  ((rationalPolynomial
                    (approximation (a, b, c, d, ε))).map
                    (algebraMap ℚ ℂ))‖ < ‖X z‖)

end

end MathlibPlus.Open.NewResearch2.R0225CompactApproximation
