import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.Analysis

def rieszMobius (n : ℕ) : ℝ := ArithmeticFunction.moebius n

def lowerIncompleteGamma (a x : ℝ) : ℝ :=
  ∫ t in Set.Ioc (0 : ℝ) x, Real.rpow t (a - 1) * Real.exp (-t)

def truncatedCriticalLogField (N : ℕ) (u : ℝ) : ℝ :=
  Real.exp (3 * u / 2) *
    ∑ n ∈ Finset.Icc 1 N,
      rieszMobius n * (n : ℝ)⁻¹ ^ 2 *
        Real.exp (-Real.exp (2 * u) / (n : ℝ) ^ 2)

def logarithmicBlockEnergy (N : ℕ) (U : ℝ) : ℝ :=
  ∫ u in Set.Ioc U (U + 1), (truncatedCriticalLogField N u) ^ 2

def logarithmicBlockFormula (N : ℕ) (U : ℝ) : ℝ :=
  let X : ℝ := Real.exp (2 * U)
  (1 / 2 : ℝ) *
    ∑ m ∈ Finset.Icc 1 N,
      ∑ n ∈ Finset.Icc 1 N,
        rieszMobius m * rieszMobius n *
          ((m : ℝ) * n : ℝ) /
            Real.rpow ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) (3 / 2 : ℝ) *
          (lowerIncompleteGamma (3 / 2 : ℝ)
              (Real.exp 2 * X * ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) /
                ((m : ℝ) ^ 2 * (n : ℝ) ^ 2)) -
            lowerIncompleteGamma (3 / 2 : ℝ)
              (X * ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) /
                ((m : ℝ) ^ 2 * (n : ℝ) ^ 2)))

/-- The exact finite logarithmic-block energy identity. -/
def claim_9337 : Prop :=
  ∀ N : ℕ, 0 < N → ∀ U : ℝ,
    logarithmicBlockEnergy N U = logarithmicBlockFormula N U

end MathlibPlus.Open.Analysis
