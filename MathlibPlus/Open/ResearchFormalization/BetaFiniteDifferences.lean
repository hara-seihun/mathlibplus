import Mathlib

namespace MathlibPlus.Open.BetaFiniteDifferences

open MeasureTheory

noncomputable def factorialBeta (a b : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, Real.rpow x (a - 1) * Real.rpow (1 - x) (b - 1)

noncomputable def factorialContribution (n : ℕ) : ℝ :=
  2 * Real.log ((n + 2 : ℝ) / (n + 1 : ℝ))

def finiteDifference : ℕ → (ℕ → ℝ) → ℕ → ℝ
  | 0, f, n => f n
  | r + 1, f, n => finiteDifference r f (n + 1) - finiteDifference r f n

noncomputable def betaAverage (n r : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..1, factorialBeta (n + t + 1) (r + 1)

noncomputable def lowerBetaEnvelope (n r : ℕ) : ℝ :=
  2 * (Nat.factorial r : ℝ) /
    (∏ j ∈ Finset.range (r + 1), ((n : ℝ) + 3 / 2 + j))

noncomputable def upperBetaEnvelope (n r : ℕ) : ℝ :=
  (Nat.factorial n : ℝ) * (Nat.factorial r : ℝ) /
      (Nat.factorial (n + r + 1) : ℝ) +
    (Nat.factorial (n + 1) : ℝ) * (Nat.factorial r : ℝ) /
      (Nat.factorial (n + r + 2) : ℝ)

def claim59556 : Prop :=
  ∀ n r : ℕ,
    (-1 : ℝ) ^ r * finiteDifference r factorialContribution n =
      2 * (∫ x in (0 : ℝ)..1,
        (x : ℝ) ^ n * (1 - x) ^ r * ((1 - x) / (-Real.log x))) ∧
    (-1 : ℝ) ^ r * finiteDifference r factorialContribution n =
      2 * betaAverage n r ∧
    2 * factorialBeta ((n : ℝ) + 3 / 2) (r + 1) <
      (-1 : ℝ) ^ r * finiteDifference r factorialContribution n ∧
    (-1 : ℝ) ^ r * finiteDifference r factorialContribution n <
      factorialBeta ((n : ℝ) + 1) (r + 1) +
        factorialBeta ((n : ℝ) + 2) (r + 1) ∧
    2 * factorialBeta ((n : ℝ) + 3 / 2) (r + 1) = lowerBetaEnvelope n r ∧
    factorialBeta ((n : ℝ) + 1) (r + 1) +
        factorialBeta ((n : ℝ) + 2) (r + 1) = upperBetaEnvelope n r

end MathlibPlus.Open.BetaFiniteDifferences
