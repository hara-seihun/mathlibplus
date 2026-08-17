import MathlibPlus.Open.ResearchFormalization.O0356.FirstPairExteriorSquare15677

open scoped BigOperators Topology
open Filter Set

namespace MathlibPlus.Open.ResearchFormalization.R2632.Claim42983

noncomputable section

open MathlibPlus.Open.ResearchFormalization.O0356.Claim15677

noncomputable def nearestInteriorShell42983
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

noncomputable def cayleyPoint42983 (ρ : HadamardZero) : ℂ :=
  (1 - 1 / ρ.1)⁻¹

noncomputable def cayleyMode42983 (ρ : HadamardZero) : ℂ :=
  cayleyPoint42983 ρ - 1

noncomputable def matchingSlope42983 (ρ : HadamardZero) : ℝ :=
  Complex.normSq (cayleyMode42983 ρ)

noncomputable def shellExcess42983 (ρ : HadamardZero) : ℝ :=
  Complex.normSq (cayleyPoint42983 ρ) - 1

def selectedConjugatePair42983
    (ρ : HadamardZero) (m : ℕ) : Prop :=
  nearestInteriorShell42983 ρ ∧
    0 < m ∧
      IsAnalyticZeroMultiplicity ρ m ∧
        poleRemovedZeta (star ρ.1) = 0 ∧
          (∀ j : ℕ, j < m →
            iteratedDeriv j poleRemovedZeta (star ρ.1) = 0) ∧
            iteratedDeriv m poleRemovedZeta (star ρ.1) ≠ 0 ∧
              (cayleyMode42983 ρ).im ≠ 0

noncomputable def poissonDerivative42983
    (S_f : ℕ → ℂ) (x : ℝ) (r : ℕ) : ℂ :=
  iteratedDeriv r
    (fun z : ℂ => poissonTransform S_f z) (x : ℂ)

noncomputable def adjacentEnergy42983
    (S_f : ℕ → ℂ) (ρ : HadamardZero) (x : ℝ) : ℝ :=
  let d := matchingSlope42983 ρ
  let r := Nat.floor (d * x)
  x ^ r / (Nat.factorial r : ℝ) *
      ‖poissonDerivative42983 S_f x r‖ ^ 2 +
    x ^ (r + 1) / (Nat.factorial (r + 1) : ℝ) *
      ‖poissonDerivative42983 S_f x (r + 1)‖ ^ 2

noncomputable def adjacentEnergyLowerScale42983
    (ρ : HadamardZero) (c x : ℝ) : ℝ :=
  c * Real.rpow x (-1 / 2 : ℝ) *
    Real.exp (shellExcess42983 ρ * x)

/-- The selected nearest false-RH Cayley shell forces the exact two adjacent
Poisson derivative channels to carry the stated exponential energy. -/
def claim_42983 : Prop :=
  ∀ (S_f : ℕ → ℂ) (ρ : HadamardZero) (m : ℕ),
    MathlibPlus.Open.ResearchFormalization.O0356.Claim15677.IsHadamardLiCoefficientSequence S_f →
      ¬ MathlibPlus.Open.ResearchFormalization.O0356.Claim15677.RiemannHypothesis →
        selectedConjugatePair42983 ρ m →
          0 < shellExcess42983 ρ ∧
            ∃ c : ℝ, 0 < c ∧
              ∀ᶠ x : ℝ in Filter.atTop,
                adjacentEnergy42983 S_f ρ x ≥
                  adjacentEnergyLowerScale42983 ρ c x

end

end MathlibPlus.Open.ResearchFormalization.R2632.Claim42983
