import Mathlib

namespace MathlibPlus.Open.Analysis

open Filter

noncomputable def principalLambertW (x : ℝ) : ℝ :=
  if 0 ≤ x then sInf {w : ℝ | 0 ≤ w ∧ w * Real.exp w = x} else 0

noncomputable def lambertWModel (x : ℝ) : ℝ :=
  principalLambertW (x / (2 * Real.pi))

noncomputable def lambertCoefficient (j : ℕ) : ℝ :=
  if 0 < j then
    lambertWModel (j : ℝ) / (4 * (j : ℝ))
  else 0

noncomputable def rowGaugeDefect (a : ℕ → ℝ) (j : ℕ) : ℝ :=
  Real.log (a j / lambertCoefficient j)

noncomputable def adjacentGaugeDefect (a : ℕ → ℝ) (j : ℕ) : ℝ :=
  rowGaugeDefect a j - rowGaugeDefect a (j + 1)

noncomputable def weightedGaugeCocycle (a : ℕ → ℝ) (m N : ℕ) : ℝ :=
  Finset.sum (Finset.Ioc m N) (fun j => rowGaugeDefect a j - rowGaugeDefect a N)

noncomputable def monicSquaredNorm (a : ℕ → ℝ) (μ₀ : ℝ) (k : ℕ) : ℝ :=
  μ₀ * Finset.prod (Finset.Icc 1 (2 * k)) (fun j => (a j) ^ 2)

noncomputable def trailingError (a : ℕ → ℕ → ℝ) (n : ℕ) (m : ℕ) : ℝ :=
  weightedGaugeCocycle (a n) m (2 * n)

noncomputable def fullError (a : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  trailingError a n 0

noncomputable def lastDefect (a : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  adjacentGaugeDefect (a n) (2 * n - 1)

noncomputable def depthAction (a : ℕ → ℕ → ℝ) (μ₀ : ℝ)
    (d : ℕ → ℕ) (n : ℕ) : ℝ :=
  Real.log
    (((a n (2 * n)) ^ (4 * d n) *
        monicSquaredNorm (a n) μ₀ (n - d n)) /
      monicSquaredNorm (a n) μ₀ n)

noncomputable def fullAction (a : ℕ → ℕ → ℝ) (μ₀ : ℝ) (n : ℕ) : ℝ :=
  Real.log
    (monicSquaredNorm (a n) μ₀ n /
      (μ₀ * (a n (2 * n)) ^ (4 * n)))

noncomputable def denominatorAction (a : ℕ → ℕ → ℝ) (μ₀ : ℝ) (n : ℕ) : ℝ :=
  if 0 < n then
    Real.log
      ((monicSquaredNorm (a n) μ₀ n *
          monicSquaredNorm (a n) μ₀ (n - 1)) /
        (μ₀ ^ 2 * (a n (2 * n)) ^ (8 * n - 4)))
  else 0

def littleOInTrailingLength (f : ℕ → ℝ) : Prop :=
  Tendsto (fun n => f n / (2 * (n : ℝ))) atTop (nhds 0)

noncomputable def macroscopicDepthProfile (τ : ℝ) : ℝ :=
  1 - τ + τ * Real.log τ

noncomputable def deterministicTransferConditionsAllThree : Prop :=
  ∀ (a : ℕ → ℕ → ℝ) (μ₀ : ℝ) (d : ℕ → ℕ) (θ : ℝ),
    0 < μ₀ →
    (∀ n j, 1 ≤ j → j ≤ 2 * n → 0 < a n j) →
    (∀ n, d n ≤ n) →
    0 ≤ θ → θ ≤ 1 →
    Tendsto (fun n => (d n : ℝ) / (n : ℝ)) atTop (nhds θ) →
    (littleOInTrailingLength (fun n =>
        trailingError a n (2 * (n - d n))) →
      Tendsto (fun n => depthAction a μ₀ d n / (n : ℝ)) atTop
        (nhds (-4 * macroscopicDepthProfile (1 - θ)))) ∧
    (littleOInTrailingLength (fullError a) →
      Tendsto (fun n => fullAction a μ₀ n / (n : ℝ)) atTop (nhds 4)) ∧
    (littleOInTrailingLength (fullError a) ∧
        littleOInTrailingLength (lastDefect a) →
      Tendsto (fun n => denominatorAction a μ₀ n / (n : ℝ)) atTop (nhds 8))

end MathlibPlus.Open.Analysis
