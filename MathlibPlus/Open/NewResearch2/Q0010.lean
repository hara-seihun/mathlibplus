import Mathlib

open scoped BigOperators
open MeasureTheory Set

namespace MathlibPlus.Open.NewResearch2.Q0010

noncomputable section

private def ratio (t : ℕ → ℝ) (n : ℕ) : ℝ := t (n + 1) / t n

private def logRatio (t : ℕ → ℝ) (n : ℕ) : ℝ := Real.log (ratio t n)

private def forwardDifference (f : ℕ → ℝ) (n : ℕ) : ℝ := f (n + 1) - f n

private def iteratedDifference : ℕ → (ℕ → ℝ) → ℕ → ℝ
  | 0, f, n => f n
  | r + 1, f, n =>
      forwardDifference (fun k => iteratedDifference r f k) n

/-- Claim 15754: the ratio and iterated forward-curvature convention. -/
def claim15754 : Prop :=
  ∀ t : ℕ → ℝ, (∀ n, 0 < t n) →
    (∀ n, ratio t n = t (n + 1) / t n) ∧
    (∀ n, logRatio t n = Real.log (ratio t n)) ∧
    (∀ r n, iteratedDifference r (logRatio t) n =
      iteratedDifference r (fun k => Real.log (t (k + 1) / t k)) n)

/-- Claim 15759: the factorial component is a positive Hausdorff moment. -/
def claim15759 : Prop :=
  ∀ n : ℕ,
    2 * Real.log (((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) =
      2 * ∫ x in Ioo (0 : ℝ) 1,
        x ^ n * (1 - x) / (-Real.log x) ∂volume ∧
    (∀ x : ℝ, x ∈ Ioo (0 : ℝ) 1 →
      0 ≤ x ^ n * (1 - x) / (-Real.log x))

end
end MathlibPlus.Open.NewResearch2.Q0010
