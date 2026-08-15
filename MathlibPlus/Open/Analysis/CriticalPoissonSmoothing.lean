import Mathlib

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Analysis

/-- The `L_{n-1}^1` polynomial appearing in the admitted finite-place moment formula. -/
noncomputable def criticalLaguerreOne (n : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n,
    (-1 : ℝ) ^ j * (Nat.choose n (j + 1) : ℝ) * t ^ j / (Nat.factorial j : ℝ)

/-- The finite-place integral expanded from the centered measure in the repair context. -/
noncomputable def criticalCenteredFinitePlaceMoment (n X : ℕ) : ℝ :=
  if 2 ≤ X then
    (∑ m ∈ Finset.Icc 1 X,
      (ArithmeticFunction.vonMangoldt m / (m : ℝ)) *
        criticalLaguerreOne n (Real.log (m : ℝ))) -
      ∫ t in Set.Icc (0 : ℝ) (Real.log (X : ℝ)), criticalLaguerreOne n t ∂volume
  else 0

/-- The exact finite-place-limit sequence used by the admitted claim, with its stated
zero-th value. -/
noncomputable def criticalSf (n : ℕ) : ℝ :=
  if 0 < n then
    Filter.limUnder Filter.atTop (criticalCenteredFinitePlaceMoment n)
  else 0

/-- The critical Poisson smoothing in Claim 10104. -/
noncomputable def criticalPoissonPhi (u : ℝ) : ℝ :=
  Real.exp (-(u ^ 2)) *
    ∑' n : ℕ,
      if 1 ≤ n then
        criticalSf n * u ^ (2 * n) / (Nat.factorial n : ℝ)
      else 0

/-- The normalized signal on its stated positive domain. -/
noncomputable def criticalNormalizedSignal (u : {u : ℝ // 0 < u}) : ℝ :=
  (criticalPoissonPhi u + 1) / Real.sqrt u

/-- The explicit Poisson mean equivalent to the smoothing formula. -/
noncomputable def criticalPoissonMean (u : ℝ) : ℝ :=
  ∑' n : ℕ,
    criticalSf n *
      (Real.exp (-(u ^ 2)) * (u ^ 2) ^ n / (Nat.factorial n : ℝ))

/-- Claim 10104: critical Poisson smoothing and normalized signal, including the
finite-place-limit identification of `S_f`, the positive-domain normalization,
and the equivalent Poisson-mean form. -/
def criticalPoissonSmoothingNormalizedSignal : Prop :=
  criticalSf 0 = 0 ∧
    (∀ n : ℕ, 0 < n →
      Filter.Tendsto (criticalCenteredFinitePlaceMoment n) Filter.atTop
        (nhds (criticalSf n))) ∧
    (∀ u : ℝ,
      criticalPoissonPhi u =
        Real.exp (-(u ^ 2)) *
          ∑' n : ℕ,
            if 1 ≤ n then
              criticalSf n * u ^ (2 * n) / (Nat.factorial n : ℝ)
            else 0) ∧
    (∀ u : {u : ℝ // 0 < u},
      criticalNormalizedSignal u =
        (criticalPoissonPhi u + 1) / Real.sqrt u) ∧
    (∀ u : ℝ, criticalPoissonPhi u = criticalPoissonMean u)

end MathlibPlus.Open.Analysis
