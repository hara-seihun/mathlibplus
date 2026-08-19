import Mathlib
import MathlibPlus.Open.Combinatorics.SquaredReciprocalEnsembles
import MathlibPlus.Open.Formalization.K0127.DifferentiationOfConcavePotentialLimits

open scoped BigOperators ENNReal Topology
open Filter MeasureTheory

namespace MathlibPlus.Open.Combinatorics.K0127

noncomputable section

/-- Claim 8936: the explicit equilibrium tail has mass `2 / π` at its
saturation edge, and the corresponding endogenous Gaussian-node tail
fraction has the same limit. -/
def claim8936 : Prop :=
  let b : ℝ := Real.pi / 2
  let rho : ℝ → ℝ := fun z =>
    2 * ∫ u in (0 : ℝ)..1,
      Set.indicator (Set.Ioo (0 : ℝ) (b / u)) (fun _ => (1 : ℝ)) z /
        (Real.pi * Real.sqrt ((b / u) ^ 2 - z ^ 2))
  let tail : ℝ → ℝ := fun z => ∫ y in Set.Ici z, rho y
  let equilibriumMeasure : Measure ℝ :=
    (Measure.restrict volume (Set.Ici (0 : ℝ))).withDensity
      (fun z => ENNReal.ofReal (rho z))
  ∀ (z x ω : ℕ → ℕ+ → ℝ)
    (P : ℕ → Finset ℕ+ → ℝ)
    (p : ℕ → Polynomial ℝ)
    (y : ∀ n : ℕ, Fin n → ℝ),
    (∀ n : ℕ,
      squaredVandermondeOrthogonalPolynomialEnsemble n z x ω (P n) ∧
        discreteHeineFormula n z x ω (p n) (P n)) →
    (∀ n : ℕ,
      (p n).Monic ∧
        (p n).natDegree = n ∧
        p n = ∏ j : Fin n,
          (Polynomial.X - Polynomial.C ((y n j) ^ 2)) ∧
        (∀ j : Fin n, 0 < y n j) ∧
        (∀ i j : Fin n, i.val < j.val → y n j < y n i)) →
    (∀ φ : ℝ → ℝ, Continuous φ →
      Bornology.IsBounded (Set.range φ) →
      Tendsto
        (fun n : ℕ =>
          ∫ t, φ t ∂
            (MathlibPlus.Open.Formalization.K0127.empiricalGaussianZeroMeasure y n))
        atTop
        (𝓝 (∫ t, φ t ∂equilibriumMeasure))) →
    IsProbabilityMeasure equilibriumMeasure →
    tail b = 2 / Real.pi ∧
      Tendsto
        (fun n : ℕ =>
          (∑ j : Fin n, if b ≤ y n j then (1 : ℝ) else 0) /
            (n : ℝ))
        atTop (𝓝 (2 / Real.pi))

end

end MathlibPlus.Open.Combinatorics.K0127
