import Mathlib

open scoped BigOperators
open Filter MeasureTheory Set

noncomputable section

namespace MathlibPlus.Open.Analysis

/-- The parameter-one generalized Laguerre polynomial used by the admitted claim.
This is the exact finite expansion supplied in the lease packet. -/
def laguerreOne_claim9805 (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n,
    (Nat.choose n j : ℝ) * (-x) ^ (j - 1) / (Nat.factorial (j - 1) : ℝ)

/-- The regularized centered von Mangoldt signed measure on `[0, log X]`. -/
noncomputable def centeredMeasure_claim9805 (X : ℕ) : SignedMeasure ℝ := by
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) (Real.log (X : ℝ)))
  letI : IsFiniteMeasure μ := by
    dsimp [μ]
    exact Real.isFiniteMeasure_restrict_Icc _ _
  exact
    (∑ m ∈ Finset.Icc 1 X,
      (ArithmeticFunction.vonMangoldt m / (m : ℝ)) •
        (Measure.dirac (Real.log (m : ℝ))).toSignedMeasure) -
      μ.toSignedMeasure

/-- Multiplication as the scalar bilinear map used for scalar signed integration. -/
def scalarBilinear_claim9805 : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.lsmul ℝ ℝ

/-- The finite centered Laguerre transform. -/
noncomputable def finiteSf_claim9805 (X n : ℕ) : ℝ :=
  (centeredMeasure_claim9805 X).integral
    (laguerreOne_claim9805 n) scalarBilinear_claim9805

/-- The finite orthogonal-projection kernel. -/
def kernel_claim9805 (M : ℕ) (x y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 M,
    laguerreOne_claim9805 n x * laguerreOne_claim9805 n y / (n : ℝ)

/-- The iterated signed-measure quadratic form of the kernel. -/
noncomputable def kernelEnergy_claim9805 (X M : ℕ) : ℝ :=
  (centeredMeasure_claim9805 X).integral
    (fun x =>
      (centeredMeasure_claim9805 X).integral
        (fun y => kernel_claim9805 M x y) scalarBilinear_claim9805)
    scalarBilinear_claim9805

/-- Exact finite and limiting energy identities from Claim 9805.
The named limiting sequence `S_f` is represented by its exact fixed-index
limit supplied by the admitted convergence context. -/
def exactFiniteAndLimitingEnergyIdentities_claim9805 : Prop :=
  ∀ (S_f : ℕ → ℝ),
    (∀ n : ℕ, 1 ≤ n →
      Tendsto (fun X : ℕ => finiteSf_claim9805 X n) atTop (nhds (S_f n))) →
    (∀ (X M : ℕ), 2 ≤ X →
        (∑ n ∈ Finset.Icc 1 M,
          (finiteSf_claim9805 X n) ^ 2 / (n : ℝ)) =
          kernelEnergy_claim9805 X M) ∧
    (∀ M : ℕ,
        (∑ n ∈ Finset.Icc 1 M,
          (S_f n) ^ 2 / (n : ℝ)) =
          Filter.limUnder atTop (fun X : ℕ => kernelEnergy_claim9805 X M)) ∧
    (∀ N : ℕ,
        (∑ n ∈ Finset.Ioc N (2 * N),
          (S_f n) ^ 2 / (n : ℝ)) =
          Filter.limUnder atTop
            (fun X : ℕ =>
              (centeredMeasure_claim9805 X).integral
                (fun x =>
                  (centeredMeasure_claim9805 X).integral
                    (fun y =>
                      kernel_claim9805 (2 * N) x y - kernel_claim9805 N x y)
                    scalarBilinear_claim9805)
                scalarBilinear_claim9805))

end MathlibPlus.Open.Analysis
