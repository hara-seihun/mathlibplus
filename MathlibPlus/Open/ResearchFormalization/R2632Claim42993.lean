import MathlibPlus.Open.ResearchFormalization.R2632Claim42983
import MathlibPlus.Open.ResearchFormalization.R2632Claim42985
import MathlibPlus.Open.ResearchFormalization.R2632Claim42992

open scoped BigOperators Topology
open Filter Set

namespace MathlibPlus.Open.ResearchFormalization.R2632.Claim42993

noncomputable section

open MathlibPlus.Open.ResearchFormalization.O0356.Claim15677
open MathlibPlus.Open.ResearchFormalization.R2632.Claim42983
open MathlibPlus.Open.ResearchFormalization.R2632.Claim42992

noncomputable def exteriorSquare42993
    (S_f : ℕ → ℂ) (ρ : HadamardZero) (x : ℝ) : ℂ :=
  PoissonTuránSquare S_f (Nat.floor (matchingSlope42983 ρ * x)) x

noncomputable def phaseFreePairLeading42993
    (ρ : HadamardZero) (m : ℕ) (x : ℝ) : ℂ :=
  let b := cayleyMode42983 ρ
  let r := Nat.floor (Complex.normSq b * x)
  (m : ℂ) ^ 2 * (b - starRingEnd ℂ b) ^ 2 *
    (Complex.normSq b : ℂ) ^ r *
      Complex.exp (((2 * b.re * x : ℝ) : ℂ))

noncomputable def normalizedExteriorRate42993
    (S_f : ℕ → ℂ) (ρ : HadamardZero) (x : ℝ) : ℝ :=
  let r := Nat.floor (matchingSlope42983 ρ * x)
  x⁻¹ * Real.log
    (1 + x ^ r / (Nat.factorial r : ℝ) *
      ‖exteriorSquare42993 S_f ρ x‖)

def certifiedFalseRHPeak42993
    (S_f : ℕ → ℂ) (ρ : HadamardZero) (m : ℕ) (d κ : ℝ) : Prop :=
  IsHadamardLiCoefficientSequence S_f ∧
    ¬ MathlibPlus.Open.ResearchFormalization.O0356.Claim15677.RiemannHypothesis ∧
      selectedConjugatePair42983 ρ m ∧
        d = matchingSlope42983 ρ ∧
          MathlibPlus.Open.ResearchFormalization.O0356.Claim15677.RelativeExponentialAsymptotic
            (exteriorSquare42993 S_f ρ)
            (phaseFreePairLeading42993 ρ m) ∧
            Filter.limsup
              (fun x : ℝ => normalizedExteriorRate42993 S_f ρ x)
              Filter.atTop = κ

/-- A certified false-RH peak uses the fixed Poisson--Charlier transform and
the exact Cayley-shell zero carrier; its slope and rate recover the zero. -/
def claim42993_falseRHPeakTomography : Prop :=
  ∀ (S_f : ℕ → ℂ) (ρ : HadamardZero) (m : ℕ) (d κ : ℝ),
    certifiedFalseRHPeak42993 S_f ρ m d κ →
      let β : ℝ := ρ.1.re
      let γ : ℝ := ρ.1.im
      let T₀ : ℝ := verifiedHeight42992
      κ = (2 * β - 1) * d ∧
        β = (1 / 2 : ℝ) * (1 + κ / d) ∧
          γ ^ 2 = 1 / d -
            (1 / 4 : ℝ) * (1 - κ / d) ^ 2 ∧
            0 < κ ∧ κ < d ∧ d < T₀⁻¹ ^ 2

end

end MathlibPlus.Open.ResearchFormalization.R2632.Claim42993
