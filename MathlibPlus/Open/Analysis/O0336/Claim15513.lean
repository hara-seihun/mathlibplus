import Mathlib

noncomputable section

open Set Filter MeasureTheory
open scoped BigOperators ENNReal MeasureTheory Topology

namespace MathlibPlus.Open.Analysis.O0336.Claim15513

/-- Finiteness and compact support for a real signed Borel measure. -/
def CompactlySupportedSignedMeasure (μ : SignedMeasure ℝ) : Prop :=
  IsFiniteMeasure μ.totalVariation ∧
    ∃ K : Set ℝ, IsCompact K ∧ μ.totalVariation Kᶜ = 0

/-- The signed integral against the real signed-measure carrier. -/
noncomputable def signedIntegralComplex (μ : SignedMeasure ℝ) (f : ℝ → ℂ) : ℂ :=
  (∫ x, f x ∂μ.toJordanDecomposition.posPart) -
    (∫ x, f x ∂μ.toJordanDecomposition.negPart)

/-- The complex notation `n⁻ˢ`, with the positive integer carrier made explicit. -/
noncomputable def naturalComplexInversePower (n : ℕ) (s : ℂ) : ℂ :=
  ((n : ℂ) ^ (-s))

/-- The shift-measure Laplace transform at a positive integer. -/
noncomputable def shiftLaplaceAt (μ : SignedMeasure ℝ) (n : ℕ) : ℂ :=
  signedIntegralComplex μ (fun α => naturalComplexInversePower n (α : ℂ))

/-- The normalized logarithm of the shifted-zeta product, using the actual
right-half-plane Dirichlet-series branch. -/
noncomputable def zetaLogRight (w : ℂ) : ℂ :=
  LSeries (fun n : ℕ =>
    ((ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ) : ℝ) : ℂ)) w

noncomputable def zetaLog (w : ℂ) : ℂ :=
  if 1 < w.re then zetaLogRight w else Complex.log (riemannZeta w)

noncomputable def shiftedZetaLog (μ : SignedMeasure ℝ) (s : ℂ) : ℂ :=
  signedIntegralComplex μ (fun α => zetaLog (s + (α : ℂ)))

noncomputable def shiftedZetaProduct (μ : SignedMeasure ℝ) (s : ℂ) : ℂ :=
  Complex.exp (shiftedZetaLog μ s)

/-- The displayed cumulative logarithmic Dirichlet series. -/
noncomputable def shiftedZetaLogDirichletSeries
    (μ : SignedMeasure ℝ) (s : ℂ) : ℂ :=
  ∑' n : {n : ℕ // 2 ≤ n},
    (((ArithmeticFunction.vonMangoldt n.1 /
          Real.log (n.1 : ℝ) : ℝ) : ℂ) *
        naturalComplexInversePower n.1 s * shiftLaplaceAt μ n.1)

/-- The ordinary Dirichlet expansion with its genuine positive-integer carrier. -/
def HasOrdinaryDirichletExpansion
    (F : ℂ → ℂ) (a : ℕ+ → ℂ) (σ₀ : ℝ) : Prop :=
  ∀ s : ℂ, σ₀ < s.re →
    Summable (fun n : ℕ+ =>
      ‖a n * naturalComplexInversePower n.1 s‖) ∧
      F s = ∑' n : ℕ+, a n * naturalComplexInversePower n.1 s

/-- In a sufficiently far right half-plane the normalized logarithm has the
von-Mangoldt expansion, and exponentiation has prime coefficient equal to the
shift-measure Laplace transform. -/
def primeCoefficientIsShiftLaplaceTransform : Prop :=
  ∀ (μ : SignedMeasure ℝ) (a : ℝ),
    μ ≠ 0 →
      CompactlySupportedSignedMeasure μ →
        IsLeast μ.totalVariation.support a →
          ∃ σ₀ : ℝ, 1 - a < σ₀ ∧
            (∀ s : ℂ, σ₀ < s.re →
              shiftedZetaLog μ s = shiftedZetaLogDirichletSeries μ s) ∧
            (∃ b : ℕ+ → ℂ,
              HasOrdinaryDirichletExpansion (shiftedZetaProduct μ) b σ₀ ∧
                ∀ (p : ℕ) (hp : Nat.Prime p),
                  b ⟨p, Nat.Prime.pos hp⟩ = shiftLaplaceAt μ p)

end MathlibPlus.Open.Analysis.O0336.Claim15513
