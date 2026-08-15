import Mathlib

open BigOperators

namespace MathlibPlus.Open.Analysis

private noncomputable def ordinaryLaguerre (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    (n.choose j : ℝ) * (-x) ^ j / (Nat.factorial j : ℝ)

private noncomputable def generalizedLaguerreOne (degree : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (degree + 1),
    ((degree + 1).choose (j + 1) : ℝ) * (-x) ^ j /
      (Nat.factorial j : ℝ)

private noncomputable def regularizedCenteredVonMangoldtTransform (X : ℝ) (n : ℕ) : ℝ :=
  (∑ m ∈ Finset.Icc 1 (Nat.floor X),
      ((ArithmeticFunction.vonMangoldt : ℕ → ℝ) m / (m : ℝ)) *
        generalizedLaguerreOne (n - 1) (Real.log (m : ℝ))) -
    ∫ t in Set.Icc (0 : ℝ) (Real.log X), generalizedLaguerreOne (n - 1) t

def exactFinitePrimeTransform_claim9800 : Prop :=
  ∀ (X : ℝ) (n : ℕ), 2 ≤ X → 1 ≤ n →
    regularizedCenteredVonMangoldtTransform X n =
      (∑ m ∈ Finset.Icc 1 (Nat.floor X),
          ((ArithmeticFunction.vonMangoldt : ℕ → ℝ) m / (m : ℝ)) *
            generalizedLaguerreOne (n - 1) (Real.log (m : ℝ))) +
        ordinaryLaguerre n (Real.log X) - 1

end MathlibPlus.Open.Analysis
