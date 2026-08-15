import Mathlib

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Analysis

/-- The parameter-one generalized Laguerre polynomial in the indexing used by Claim 9802. -/
noncomputable def generalizedLaguerreOne (k : ℕ) (x : ℝ) : ℝ :=
  Finset.sum (Finset.Icc 1 (k + 1)) (fun j =>
    (Nat.choose (k + 1) j : ℝ) * (-x) ^ (j - 1) /
      (Nat.factorial (j - 1) : ℝ))

/-- The squared `L²(t exp(-t) dt)` norm on the nonnegative half-line. -/
noncomputable def generalizedLaguerreOneSquaredNorm (k : ℕ) : ℝ :=
  ∫ t in Set.Ici (0 : ℝ),
    t * Real.exp (-t) * (generalizedLaguerreOne k t) ^ 2 ∂MeasureTheory.volume

/-- The finite orthogonal-projection kernel formed from these basis functions. -/
noncomputable def generalizedLaguerreProjectionKernel (M : ℕ) (x y : ℝ) : ℝ :=
  Finset.sum (Finset.Icc 1 M) (fun n =>
    generalizedLaguerreOne (n - 1) x *
        generalizedLaguerreOne (n - 1) y /
      generalizedLaguerreOneSquaredNorm (n - 1))

/--
The associated-Laguerre orthogonality norm and the resulting normalization of
its projection-kernel terms.
-/
noncomputable def associatedLaguerreOrthogonalityNormAndKernelCoefficient_claim9802 : Prop :=
  ∀ k : ℕ,
    generalizedLaguerreOneSquaredNorm k = ((k + 1 : ℕ) : ℝ) ∧
      ∀ (M : ℕ) (x y : ℝ),
        generalizedLaguerreProjectionKernel M x y =
          Finset.sum (Finset.Icc 1 M) (fun n =>
            generalizedLaguerreOne (n - 1) x *
                generalizedLaguerreOne (n - 1) y /
              (n : ℝ))

end MathlibPlus.Open.Analysis
