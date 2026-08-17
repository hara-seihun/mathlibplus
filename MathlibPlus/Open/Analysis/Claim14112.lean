import Mathlib
import MathlibPlus.Open.Analysis.SlitPrimeEndpointCosts

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.Analysis

/-- The coefficient-series realization of a prime-log element at a complex
argument. -/
noncomputable def primeLogSeries14112
    (g : SlitPrimeLogH) (s : ℂ) : ℂ :=
  ∑' p : PrimeIndex, g.1 p * ((p.1 : ℂ) ^ (-s))

/-- The squared norm on the reviewed square-summable prime carrier. -/
noncomputable def primeLogNormSquared14112 (g : SlitPrimeLogH) : ℝ :=
  slitPrimeLogNorm g ^ 2

/-- Claim 14112: on the slit endpoints, the square-summable prime-log
carrier is realized by its coefficient series and its endpoint functional is
both the endpoint difference and the displayed coefficient series. -/
def claim14112 : Prop :=
  ∀ (a_ell b_ell : ℂ),
    (1 / 2 : ℝ) < a_ell.re ∧
      a_ell.re < 1 ∧
      (1 / 2 : ℝ) < b_ell.re ∧
      b_ell.re < 1 →
      (∀ g : SlitPrimeLogH,
        primeLogNormSquared14112 g =
          ∑' p : PrimeIndex, ‖g.1 p‖ ^ 2) ∧
      (∀ g : SlitPrimeLogH,
        slitPrimeEndpointLambda a_ell b_ell g =
          primeLogSeries14112 g b_ell -
            primeLogSeries14112 g a_ell) ∧
      (∀ g : SlitPrimeLogH,
        slitPrimeEndpointLambda a_ell b_ell g =
          ∑' p : PrimeIndex,
            g.1 p *
              ((p.1 : ℂ) ^ (-b_ell) - (p.1 : ℂ) ^ (-a_ell)))

end MathlibPlus.Open.Analysis
