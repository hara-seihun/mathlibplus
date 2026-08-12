import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

open MeasureTheory

namespace MathlibPlus.Analysis.Claim15758

/-- Forward difference in the sequence index used by claim 15758. -/
def forwardDifference (f : ℕ → ℝ) : ℕ → ℝ :=
  fun n => f (n + 1) - f n

/-- The `r`-fold forward difference, with the source's convention that the
first difference is `f (n+1)-f n`. -/
def iteratedForwardDifference (r : ℕ) (f : ℕ → ℝ) : ℕ → ℝ :=
  (forwardDifference^[r]) f

end MathlibPlus.Analysis.Claim15758

namespace MathlibPlus.Open.Analysis

/-- Claim 15758.  The measure is represented on the subtype `0 ≤ x ≤ 1`.
The source does not state its integrability convention; the antecedent keeps
that required analytic side condition explicit rather than silently changing
an integral into a finite sum or a pointwise assertion. -/
def higherDifferenceMoment_claim15758 : Prop :=
  ∀ (f : ℕ → ℝ) (μ : Measure (Set.Icc (0 : ℝ) 1)),
    (∀ n : ℕ, Integrable (fun x : Set.Icc (0 : ℝ) 1 => (x : ℝ) ^ n) μ) →
    (∀ n : ℕ,
      -MathlibPlus.Analysis.Claim15758.forwardDifference f n =
        ∫ x : Set.Icc (0 : ℝ) 1, (x : ℝ) ^ n ∂μ) →
    ∀ n r : ℕ, 1 ≤ r →
      MathlibPlus.Analysis.Claim15758.iteratedForwardDifference r f n =
          -∫ x : Set.Icc (0 : ℝ) 1,
            (x : ℝ) ^ n * ((x : ℝ) - 1) ^ (r - 1) ∂μ ∧
      0 ≤ (-1 : ℝ) ^ r *
        MathlibPlus.Analysis.Claim15758.iteratedForwardDifference r f n

end MathlibPlus.Open.Analysis
