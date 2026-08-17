import MathlibPlus.Open.ResearchFormalization.O0356.FirstPairExteriorSquare15677

open scoped BigOperators Topology
open Filter Set

namespace MathlibPlus.Open.ResearchFormalization.R2632.Claim42985

noncomputable section

open MathlibPlus.Open.ResearchFormalization.O0356.Claim15677

noncomputable def nearestInteriorShell42985
    (ρ : HadamardZero) : Prop :=
  let w : ℂ := 1 - 1 / ρ.1
  (1 / 2 : ℝ) < ρ.1.re ∧
    ρ.1.re < 1 ∧
      ρ.1.im ≠ 0 ∧
        0 < ‖w‖ ∧
          ‖w‖ < 1 ∧
            ∀ σ : HadamardZero,
              (1 / 2 : ℝ) < σ.1.re →
                σ.1.re < 1 →
                  0 < ‖1 - 1 / σ.1‖ →
                    ‖1 - 1 / σ.1‖ < 1 →
                      ‖w‖ ≤ ‖1 - 1 / σ.1‖

noncomputable def cayleyPoint42985 (ρ : HadamardZero) : ℂ :=
  (1 - 1 / ρ.1)⁻¹

noncomputable def cayleyMode42985 (ρ : HadamardZero) : ℂ :=
  cayleyPoint42985 ρ - 1

noncomputable def matchingSlope42985 (ρ : HadamardZero) : ℝ :=
  Complex.normSq (cayleyMode42985 ρ)

noncomputable def shellExcess42985 (ρ : HadamardZero) : ℝ :=
  Complex.normSq (cayleyPoint42985 ρ) - 1

def selectedConjugatePair42985
    (ρ : HadamardZero) (m : ℕ) : Prop :=
  nearestInteriorShell42985 ρ ∧
    0 < m ∧
      IsAnalyticZeroMultiplicity ρ m ∧
        poleRemovedZeta (star ρ.1) = 0 ∧
          (∀ j : ℕ, j < m →
            iteratedDeriv j poleRemovedZeta (star ρ.1) = 0) ∧
            iteratedDeriv m poleRemovedZeta (star ρ.1) ≠ 0 ∧
              (cayleyMode42985 ρ).im ≠ 0

noncomputable def exteriorSquare42985
    (S_f : ℕ → ℂ) (ρ : HadamardZero) (x : ℝ) : ℂ :=
  PoissonTuránSquare S_f
    (Nat.floor (matchingSlope42985 ρ * x)) x

noncomputable def phaseFreePairLeading42985
    (ρ : HadamardZero) (m : ℕ) (x : ℝ) : ℂ :=
  let b := cayleyMode42985 ρ
  let r := Nat.floor (Complex.normSq b * x)
  (m : ℂ) ^ 2 * (b - starRingEnd ℂ b) ^ 2 *
    (Complex.normSq b : ℂ) ^ r *
      Complex.exp (((2 * b.re * x : ℝ) : ℂ))

noncomputable def normalizedExteriorSquare42985
    (S_f : ℕ → ℂ) (ρ : HadamardZero) (x : ℝ) : ℝ :=
  let b := cayleyMode42985 ρ
  let r := Nat.floor (Complex.normSq b * x)
  x ^ r / (Nat.factorial r : ℝ) *
    ‖exteriorSquare42985 S_f ρ x‖

noncomputable def normalizedLowerScale42985
    (ρ : HadamardZero) (c x : ℝ) : ℝ :=
  c * Real.rpow x (-1 / 2 : ℝ) *
    Real.exp (shellExcess42985 ρ * x)

/-- The phase-free selected-pair asymptotic, its Stirling-scale consequence,
and its fixed negative real leading coefficient. -/
def claim_42985 : Prop :=
  ∀ (S_f : ℕ → ℂ) (ρ : HadamardZero) (m : ℕ),
    MathlibPlus.Open.ResearchFormalization.O0356.Claim15677.IsHadamardLiCoefficientSequence S_f →
      ¬ MathlibPlus.Open.ResearchFormalization.O0356.Claim15677.RiemannHypothesis →
        selectedConjugatePair42985 ρ m →
          MathlibPlus.Open.ResearchFormalization.O0356.Claim15677.RelativeExponentialAsymptotic
              (exteriorSquare42985 S_f ρ)
              (phaseFreePairLeading42985 ρ m) ∧
            (∃ c : ℝ, 0 < c ∧
              ∀ᶠ x : ℝ in Filter.atTop,
                normalizedExteriorSquare42985 S_f ρ x ≥
                  normalizedLowerScale42985 ρ c x) ∧
              let b := cayleyMode42985 ρ
              b.im ≠ 0 ∧
                (b - starRingEnd ℂ b) ^ 2 =
                  ((-4 * b.im ^ 2 : ℝ) : ℂ) ∧
                  ((b - starRingEnd ℂ b) ^ 2).re < 0

end

end MathlibPlus.Open.ResearchFormalization.R2632.Claim42985
