import Mathlib

noncomputable section

open Set Filter MeasureTheory
open scoped BigOperators ENNReal MeasureTheory Topology

namespace MathlibPlus.Open.Analysis.O0336.Claim15511

/-- Finiteness and compact support for a real signed Borel measure, expressed
through its actual total-variation measure. -/
def CompactlySupportedSignedMeasure (μ : SignedMeasure ℝ) : Prop :=
  IsFiniteMeasure μ.totalVariation ∧
    ∃ K : Set ℝ, IsCompact K ∧ μ.totalVariation Kᶜ = 0

/-- The signed integral of a complex-valued function, using the Jordan
 decomposition supplied by Mathlib's signed-measure carrier. -/
noncomputable def signedIntegralComplex (μ : SignedMeasure ℝ) (f : ℝ → ℂ) : ℂ :=
  (∫ x, f x ∂μ.toJordanDecomposition.posPart) -
    (∫ x, f x ∂μ.toJordanDecomposition.negPart)

/-- The normalized logarithm of zeta on the right half-plane, given by its
absolutely convergent von-Mangoldt Dirichlet series. -/
noncomputable def zetaLogRight (w : ℂ) : ℂ :=
  LSeries (fun n : ℕ =>
    ((ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ) : ℝ) : ℂ)) w

/-- A concrete totalization of the chosen zeta logarithm; only the right-half
plane branch is used by the shifted-zeta product below. -/
noncomputable def zetaLog (w : ℂ) : ℂ :=
  if 1 < w.re then zetaLogRight w else Complex.log (riemannZeta w)

/-- The normalized logarithm of the shifted-zeta product. -/
noncomputable def shiftedZetaLog (μ : SignedMeasure ℝ) (s : ℂ) : ℂ :=
  signedIntegralComplex μ (fun α => zetaLog (s + (α : ℂ)))

/-- The shifted-zeta product obtained by exponentiating the chosen logarithm. -/
noncomputable def shiftedZetaProduct (μ : SignedMeasure ℝ) (s : ℂ) : ℂ :=
  Complex.exp (shiftedZetaLog μ s)

/-- A nonzero single-valued meromorphic continuation of the shifted-zeta
product to a neighborhood of the lower support edge. -/
def HasNonzeroMeromorphicContinuation (μ : SignedMeasure ℝ) (a : ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧
    ∃ F : ℂ → ℂ,
      MeromorphicOn F (Metric.ball ((1 : ℂ) - (a : ℂ)) r) ∧
      (∃ z ∈ Metric.ball ((1 : ℂ) - (a : ℂ)) r, F z ≠ 0) ∧
      (∀ z : ℂ, z ∈ Metric.ball ((1 : ℂ) - (a : ℂ)) r →
        1 - a < z.re → F z = shiftedZetaProduct μ z)

/-- A finite local atomic representation with nonzero integer masses. -/
def LocallyIntegerAtomic (μ : SignedMeasure ℝ) (a : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧
    ∃ m : ℕ, ∃ α : Fin (m + 1) → ℝ, ∃ c : Fin (m + 1) → ℤ,
      α 0 = a ∧
      (∀ j, c j ≠ 0) ∧
      (∀ j, a ≤ α j ∧ α j < a + δ) ∧
      μ.restrict (Set.Ico a (a + δ)) =
        ∑ j : Fin (m + 1), ((c j : ℝ) • (Measure.dirac (α j)).toSignedMeasure)

/-- Meromorphic continuation at the lower edge forces the signed shift
measure to be locally a finite sum of nonzero integer atoms. -/
def meromorphicShiftedZetaMeasuresAreLocallyIntegerAtomic : Prop :=
  ∀ (μ : SignedMeasure ℝ) (a : ℝ),
    μ ≠ 0 →
      CompactlySupportedSignedMeasure μ →
        IsLeast μ.totalVariation.support a →
          HasNonzeroMeromorphicContinuation μ a →
            LocallyIntegerAtomic μ a

end MathlibPlus.Open.Analysis.O0336.Claim15511
