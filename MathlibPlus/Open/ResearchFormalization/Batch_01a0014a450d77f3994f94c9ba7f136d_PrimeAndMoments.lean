import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalizationBatch

open MeasureTheory

/-- The finite prime cutoff used by the two prime-sum claims. -/
def primeCutoff (y : ℕ) : Finset ℕ :=
  (Finset.Iic y).filter Nat.Prime

/-- The real prime sum L_y(σ). -/
def primeWeightSum (σ : ℝ) (y : ℕ) : ℝ :=
  ∑ p ∈ primeCutoff y, Real.rpow (p : ℝ) (-σ)

/-- The complex summand p^(-σ-it), written using the positive-real logarithm branch. -/
def primePhasePower (σ t : ℝ) (p : ℕ) : ℂ :=
  Complex.exp (-((σ : ℂ) + Complex.I * (t : ℂ)) * Complex.log (p : ℂ))

/-- The finite Dirichlet prime sum P_y(σ+it). -/
def primeDirichletSum (σ t : ℝ) (y : ℕ) : ℂ :=
  ∑ p ∈ primeCutoff y, primePhasePower σ t p

/-- The weighted logarithmic prime sum appearing in the derivative bound. -/
def primeLogWeightSum (σ : ℝ) (y : ℕ) : ℝ :=
  ∑ p ∈ primeCutoff y, Real.rpow (p : ℝ) (-σ) * Real.log (p : ℝ)

/-- The t-derivative of the finite prime sum. -/
def primeDirichletDerivative (σ t : ℝ) (y : ℕ) : ℂ :=
  ∑ p ∈ primeCutoff y,
    (-Complex.I * Complex.log (p : ℂ)) * primePhasePower σ t p

/-- Claim 13421: the weighted prime-sum asymptotic and its coherent edge phase. -/
def claim_13421_weighted_prime_sum_asymptotic_and_edge_phase : Prop :=
  ∀ σ : ℝ, 1 / 2 < σ → σ < 1 →
    Asymptotics.IsEquivalent Filter.atTop
      (primeWeightSum σ)
      (fun y : ℕ =>
        Real.rpow (y : ℝ) (1 - σ) / ((1 - σ) * Real.log (y : ℝ))) ∧
    Asymptotics.IsEquivalent Filter.atTop
      (fun y : ℕ => primeDirichletSum σ (Real.pi / Real.log (y : ℝ)) y)
      (fun y : ℕ => -(primeWeightSum σ y : ℂ))

/-- Claim 13422: the derivative bound, big-O estimate, and shrinking coherent edge packet. -/
def claim_13422_stability_width_of_the_coherent_edge_packet : Prop :=
  ∀ σ : ℝ, 1 / 2 < σ → σ < 1 →
    (∀ (y : ℕ) (t : ℝ),
      ‖primeDirichletDerivative σ t y‖ ≤ primeLogWeightSum σ y) ∧
    Asymptotics.IsBigO Filter.atTop
      (primeLogWeightSum σ)
      (fun y : ℕ => primeWeightSum σ y * Real.log (y : ℝ)) ∧
    ∃ ε : ℕ → ℝ,
      Filter.Tendsto ε Filter.atTop (nhds 0) ∧
      ∀ᶠ y : ℕ in Filter.atTop,
        ∀ t : ℝ,
          |t - Real.pi / Real.log (y : ℝ)| ≤
              1 / (Real.log (y : ℝ) * Real.sqrt (primeWeightSum σ y)) →
          -(primeDirichletSum σ t y).re ≥
            (1 - ε y) * primeWeightSum σ y

/-- The unit-rate Gamma density of shape α on the nonnegative real half-line. -/
def unitRateGammaDensity (α v : ℝ) : ℝ :=
  if 0 ≤ v then
    Real.rpow v (α - 1) * Real.exp (-v) / Real.Gamma α
  else 0

/-- Claim 13434: the first two moments of the normalized unit-rate Gamma law. -/
def claim_13434_first_two_gamma_moments : Prop :=
  ∀ α : ℝ, 0 < α →
    (∫ v : ℝ, v * unitRateGammaDensity α v
        ∂(volume.restrict (Set.Ici (0 : ℝ))) = α) ∧
    (∫ v : ℝ, v ^ 2 * unitRateGammaDensity α v
        ∂(volume.restrict (Set.Ici (0 : ℝ))) = α * (α + 1))

end MathlibPlus.Open.ResearchFormalizationBatch
