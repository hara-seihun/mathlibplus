import MathlibPlus.Open.ResearchFormalization.R2063Claim35959

open scoped BigOperators
open Filter
open MathlibPlus.Open.NumberTheory.Claim35956

namespace MathlibPlus.Open.ResearchFormalization.R2063Claim35957

noncomputable section

private def criticalMultiplicityLog : ℕ → ℝ :=
  fun N =>
    Real.log
      (simultaneousPrimeMaximizerCount N (criticalScale N) : ℝ)

private def criticalPrimorialLog : ℕ → ℝ :=
  fun N => Real.log (primorial (criticalScale N) : ℝ)

private def criticalFractionLog : ℕ → ℝ :=
  fun N =>
    Real.log
      ((simultaneousPrimeMaximizerCount N (criticalScale N) : ℝ) /
        (primorial (criticalScale N) : ℝ))

/-- Claim 35957: at the critical scale, the simultaneous adverse-shift
    multiplicity has full critical logarithmic mass, equivalently full
    primorial exponent up to a little-o loss. -/
def criticalPrimeLayerMultiplicity_claim35957 : Prop :=
  Asymptotics.IsEquivalent atTop
    criticalMultiplicityLog criticalScale ∧
    Asymptotics.IsEquivalent atTop
      criticalMultiplicityLog criticalPrimorialLog ∧
      Asymptotics.IsLittleO atTop
        criticalFractionLog criticalPrimorialLog

end

end MathlibPlus.Open.ResearchFormalization.R2063Claim35957
