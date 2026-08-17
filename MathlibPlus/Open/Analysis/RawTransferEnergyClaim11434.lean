import Mathlib
import MathlibPlus.Open.Analysis.AdmittedO0098

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.RawTransferEnergyClaim11434

noncomputable section

/-- The weighted prime sum at the same sharp cutoff as `transferEnergy`. -/
noncomputable def rawPrimeWeightSum (σ : ℝ) (P : ℕ) : ℝ :=
  ∑ q ∈ primesUpTo P, primeWeight σ q

/-- Claim 11434: the raw finite-prime transfer energy has the two-step
asymptotic and its critical specialization. -/
def claim11434 : Prop :=
  (∀ σ : ℝ, 0 < σ → σ < 1 →
    Asymptotics.IsEquivalent Filter.atTop
      (fun P : ℕ => Real.log (transferEnergy σ P))
      (fun P : ℕ => 2 * rawPrimeWeightSum σ P) ∧
      Asymptotics.IsEquivalent Filter.atTop
        (fun P : ℕ => 2 * rawPrimeWeightSum σ P)
        (fun P : ℕ =>
          2 * Real.rpow (P : ℝ) (1 - σ) /
            ((1 - σ) * Real.log (P : ℝ)))) ∧
    Asymptotics.IsEquivalent Filter.atTop
      (fun P : ℕ => Real.log (transferEnergy (1 / 2 : ℝ) P))
      (fun P : ℕ => 4 * Real.sqrt (P : ℝ) / Real.log (P : ℝ))

end

end MathlibPlus.Open.Analysis.RawTransferEnergyClaim11434
