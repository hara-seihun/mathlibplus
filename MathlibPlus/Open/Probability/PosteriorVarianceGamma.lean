import Mathlib

open scoped BigOperators
open MeasureTheory
open ProbabilityTheory

namespace MathlibPlus.Open.Probability

noncomputable section

/-- Expectation with respect to a finitely supported probability weight. -/
def weightedMean {Ω : Type} [Fintype Ω] (w f : Ω → ℝ) : ℝ :=
  ∑ x : Ω, w x * f x

/-- Variance under the finite weight `w`. -/
def weightedVariance {Ω : Type} [Fintype Ω] (w f : Ω → ℝ) : ℝ :=
  weightedMean w (fun x => (f x - weightedMean w f) ^ 2)

/-- Covariance under the finite weight `w`. -/
def weightedCovariance {Ω : Type} [Fintype Ω] (w f g : Ω → ℝ) : ℝ :=
  weightedMean w (fun x =>
    (f x - weightedMean w f) * (g x - weightedMean w g))

/-- Claim 47583: the nodewise variance decomposition and its nonnegative
covariance correction, with the posterior fibre represented by a finite
probability weight. -/
def claim47583 : Prop :=
  ∀ {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (w : Ω → ℝ) (a s : ℝ) (h v : Ω → ℝ),
    (∀ x, 0 ≤ w x) ∧
      (∑ x : Ω, w x = 1) ∧
      0 ≤ a ∧ 0 ≤ s - a ∧
      (∀ x, h x = (-1 : ℝ) ∨ h x = 1) ∧
      (∀ x, -1 ≤ v x ∧ v x ≤ 1) →
    let r := s - a
    let g := fun x => a * h x + r * v x
    weightedVariance w g =
        (s ^ 2 - r ^ 2) + r ^ 2 * weightedVariance w v -
          (a ^ 2 * (1 - weightedVariance w h) +
            2 * a * r * (1 - weightedCovariance w h v)) ∧
      0 ≤ a ^ 2 * (1 - weightedVariance w h) +
        2 * a * r * (1 - weightedCovariance w h v)

/-- Claim 47584: the persistent-list identity for a finite collection of
reached active nodes.  The weights `p` are the node probabilities, while `w`
is the conditional posterior weight on each node; no optimality predicate is
assumed. -/
def claim47584 : Prop :=
  ∀ {Ω ι : Type} [Fintype Ω] [Fintype ι] [DecidableEq Ω] [DecidableEq ι]
    (p : ι → ℝ) (w : ι → Ω → ℝ) (a s : ℝ)
    (h v : ι → Ω → ℝ),
    (∀ z, 0 ≤ p z) ∧
      (∀ z, (∀ x, 0 ≤ w z x) ∧ (∑ x : Ω, w z x = 1)) ∧
      0 ≤ a ∧ 0 ≤ s - a ∧
      (∀ z x, h z x = (-1 : ℝ) ∨ h z x = 1) ∧
      (∀ z x, -1 ≤ v z x ∧ v z x ≤ 1) →
    let r := s - a
    let g := fun z x => a * h z x + r * v z x
    let qT := ∑ z : ι, p z
    let P := fun f : ι → Ω → ℝ =>
      ∑ z : ι, p z * weightedVariance (w z) (f z)
    let Xi :=
      ∑ z : ι, p z *
        (a ^ 2 * (1 - weightedVariance (w z) (h z)) +
          2 * a * r * (1 - weightedCovariance (w z) (h z) (v z)))
    0 ≤ Xi ∧
      P g = (s ^ 2 - r ^ 2) * qT +
        P (fun z x => r * v z x) - Xi

/-- The shape-five-fourths, rate-one gamma law used in the rank-six wall
obstruction. -/
noncomputable def gammaFiveFourths : Measure ℝ :=
  ProbabilityTheory.gammaMeasure (5 / 4 : ℝ) 1

noncomputable def gammaLogVariable (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (Real.pi / t)

noncomputable def gammaEvenMoment (j : ℕ) (y : ℝ) : ℝ :=
  ∫ t : ℝ, (y + gammaLogVariable t) ^ (2 * j) ∂gammaFiveFourths

noncomputable def gammaWallWronskian (y : ℝ) : ℝ :=
  Matrix.det (fun i j : Fin 6 ↦
    iteratedDeriv (i : ℕ) (gammaEvenMoment (j : ℕ)) y)

/-- Claim 47599: the certified strict negative rank-six wall Wronskian at
`log 34`, with the Gamma(5/4,1) law and the logarithmic random variable made
explicit. -/
def claim47599 : Prop :=
  gammaWallWronskian (Real.log 34) < -(19 / 10 : ℝ) * 10 ^ 14

end

end MathlibPlus.Open.Probability
