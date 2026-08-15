import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.AnalyticNumberTheory.MobiusDensity

noncomputable section

def mobiusDensity (m : ℕ) : ℝ :=
  ∏ q ∈ m.primeFactors, (q : ℝ) / (q + 1)

def correctedResidueWeight (Q k : ℕ) : ℝ :=
  1 / ((k : ℝ) *
    ∏ q ∈ (k.primeFactors.filter (fun q => ¬ q ∣ Q)), (q : ℝ) + 1)

def mobiusDensityAndCorrectedResidueWeight : Prop :=
  ∀ (N n : ℕ), N ∣ n →
    (∀ m : ℕ,
      mobiusDensity m =
        ∏ q ∈ m.primeFactors, (q : ℝ) / (q + 1)) ∧
    (∀ k : ℕ,
      correctedResidueWeight (n / N) k =
        1 / ((k : ℝ) *
          ∏ q ∈ (k.primeFactors.filter (fun q => ¬ q ∣ (n / N))),
            (q : ℝ) + 1))

end

end MathlibPlus.Open.AnalyticNumberTheory.MobiusDensity
