import MathlibPlus.Open.Analysis.GammaReadout

namespace MathlibPlus.Open.Analysis

noncomputable section

open MeasureTheory
open scoped BigOperators Interval

/-- The Gamma expectation in the positive-axis integral (9). -/
def gammaPhiIntegral50146 (m : ℕ) (q : ℝ) (v : ℂ) : ℂ :=
  gammaExpectationComplex (fun t =>
    gammaE m (v * ((1 : ℂ) - (q : ℂ) * (t : ℂ))))

/-- The endpoint-singular integrand occurring in (6b). -/
def gammaPhiEndpointIntegrand50146 (m : ℕ) (q : ℝ) (v : ℂ)
    (ell : ℕ) (t : ℝ) : ℂ :=
  ((Complex.exp (v * (t : ℂ)) *
      Complex.cpow (1 + (q : ℂ) * v * (t : ℂ)) (-(gammaShape : ℂ)) - 1) /
      (t : ℂ)) *
    (gammaL t : ℂ) ^ (m - 2 * ell - 1)

/-- The explicit representation (6b), with the stated factorial
normalizations and finite range of `ell`. -/
def gammaPhiAlternative50146 (m : ℕ) (q : ℝ) (v : ℂ) : ℂ :=
  Finset.sum (Finset.range (((m - 1) / 2) + 1)) (fun ell =>
    ((m.factorial : ℂ) * (-1 : ℂ) ^ ell * (Real.pi : ℂ) ^ (2 * ell) /
        ((2 * ell + 1).factorial : ℂ) /
      (m - 2 * ell - 1).factorial) *
      intervalIntegral (gammaPhiEndpointIntegrand50146 m q v ell) (0 : ℝ) 1
        volume)

/-- Claim 50146: the positive-axis Gamma integral is absolutely convergent,
agrees with the filtered germ in its convergence disk, is holomorphic at
positive-axis points, and has the equivalent endpoint-integrable formula
(6b) in the right half-plane. -/
def claim50146 : Prop :=
  ∀ (m : ℕ), 1 ≤ m →
    ∀ (q : ℝ), 0 < q →
      (∀ v : ℝ, 0 ≤ v →
        IntegrableOn
          (fun t : ℝ =>
            (gammaDensity t : ℂ) *
              gammaE m
                ((v : ℂ) * ((1 : ℂ) - (q : ℂ) * (t : ℂ))))
          (Set.Ioi (0 : ℝ))) ∧
      (∀ v : ℂ, ‖v‖ < q⁻¹ →
        gammaPhiIntegral50146 m q v = gammaPhi m q v) ∧
      (∀ x : ℝ, 0 < x →
        AnalyticAt ℂ (gammaPhiIntegral50146 m q) (x : ℂ)) ∧
      (∀ v : ℂ, 0 < v.re →
        gammaPhiIntegral50146 m q v = gammaPhiAlternative50146 m q v ∧
          ∀ ell ∈ Finset.range (((m - 1) / 2) + 1),
            IntegrableOn
              (gammaPhiEndpointIntegrand50146 m q v ell)
              (Set.Ioo (0 : ℝ) 1))

end

end MathlibPlus.Open.Analysis
