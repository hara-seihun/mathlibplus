import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.Analysis

/-- Registry statement for admitted claim 4325.  The endpoint-flat source,
finite arithmetic kernel, Fourier convention, and the exact positive-frequency
Poisson splitting are all written in the declaration; no regularity or
integrability hypothesis beyond the source contract is added. -/
def exactPoissonSplitting_claim4325 : Prop :=
  ∀ (c : ℝ), 0 < c →
    ∀ (p : ℝ → ℝ),
    (Function.Even p ∧
      Function.support p ⊆ Set.Icc (-1) 1 ∧
      (∫ v : ℝ, p v) = 0 ∧
      p 1 = 0) →
      let K : ℝ → ℝ := fun x =>
        Real.exp (x / 2) / Real.sqrt c *
          ∑ n ∈
            (Finset.Icc 1 (Nat.ceil (c * Real.exp (-x)))).filter
              (fun n : ℕ => (n : ℝ) < c * Real.exp (-x)),
            p ((n : ℝ) * Real.exp x / c)
      let pHat : ℝ → ℂ := fun ξ =>
        ∫ v in (-1 : ℝ)..1,
          (p v : ℂ) *
            Complex.exp
              (-2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ) * (v : ℂ))
      ∀ x : ℝ,
        (K x : ℂ) =
          ((-p 0 / (2 * Real.sqrt c) * Real.exp (x / 2) : ℝ) : ℂ) +
            ((Real.sqrt c * Real.exp (-x / 2) : ℝ) : ℂ) *
              ∑' k : ℕ,
                if 1 ≤ k then pHat ((k : ℝ) * c * Real.exp (-x)) else 0

end MathlibPlus.Open.Analysis
