import Mathlib

namespace MathlibPlus.Open.Formalization.K0127

open MeasureTheory
open scoped BigOperators ENNReal Topology

noncomputable section

/-- The empirical measure of the positive Gaussian nodes at level `n`. -/
def empiricalGaussianZeroMeasure
    (y : ∀ n : ℕ, Fin n → ℝ) (n : ℕ) : Measure ℝ :=
  ((n : ℝ≥0∞)⁻¹) • ∑ j : Fin n, Measure.dirac (y n j)

/-- The finite logarithmic potential, normalized at `s₀`. -/
def gaussianLogPotential
    (ν : Measure ℝ) (s₀ s : ℝ) : ℝ :=
  ∫ z, Real.log ((s + z ^ 2) / (s₀ + z ^ 2)) ∂ν

/-- The limiting logarithmic potential of the density `ρStar`, normalized at `s₀`. -/
def equilibriumLogPotential
    (ρStar : ℝ → ℝ) (s₀ s : ℝ) : ℝ :=
  ∫ z, Real.log ((s + z ^ 2) / (s₀ + z ^ 2)) * ρStar z
    ∂(volume.restrict (Set.Ioi (0 : ℝ)))

/--
Pointwise convergence of the concave differentiable Gaussian-node logarithmic
potentials to a differentiable equilibrium potential gives convergence of the
derivatives and, through their Stieltjes-transform identities, convergence of
the displayed integrals.
-/
def differentiationOfConcavePotentialLimits
    (y : ∀ n : ℕ, Fin n → ℝ)
    (ρStar : ℝ → ℝ) : Prop :=
  (∀ n : ℕ, ∀ j : Fin n, 0 < y n j) ∧
  (∀ n : ℕ, ∀ i j : Fin n, i.val < j.val → y n j < y n i) ∧
  (∀ s₀ : ℝ, 0 < s₀ →
    ((∀ n : ℕ,
        ConcaveOn ℝ (Set.Ioi (0 : ℝ))
          (gaussianLogPotential (empiricalGaussianZeroMeasure y n) s₀)) ∧
      (∀ n : ℕ,
        DifferentiableOn ℝ
          (gaussianLogPotential (empiricalGaussianZeroMeasure y n) s₀)
          (Set.Ioi (0 : ℝ))) ∧
      DifferentiableOn ℝ (equilibriumLogPotential ρStar s₀)
        (Set.Ioi (0 : ℝ)) ∧
      (∀ s : ℝ, 0 < s →
        Filter.Tendsto
          (fun n : ℕ =>
            gaussianLogPotential (empiricalGaussianZeroMeasure y n) s₀ s)
          Filter.atTop
          (𝓝 (equilibriumLogPotential ρStar s₀ s)))) →
    ((∀ s : ℝ, 0 < s →
        Filter.Tendsto
          (fun n : ℕ =>
            deriv (gaussianLogPotential (empiricalGaussianZeroMeasure y n) s₀) s)
          Filter.atTop
          (𝓝 (deriv (equilibriumLogPotential ρStar s₀) s))) ∧
      (∀ s : ℝ, 0 < s →
        Filter.Tendsto
          (fun n : ℕ =>
            ∫ z, (s + z ^ 2)⁻¹
              ∂(empiricalGaussianZeroMeasure y n))
          Filter.atTop
          (𝓝 (∫ z, (s + z ^ 2)⁻¹ * ρStar z
            ∂(volume.restrict (Set.Ioi (0 : ℝ))))))))

end
end MathlibPlus.Open.Formalization.K0127
