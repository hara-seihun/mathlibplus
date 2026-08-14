import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatch

/-!
The product-span carrier in Claims 22086, 22088, and 22143 is represented by
`MvPolynomial (Fin 2) ℚ`, with variables `0` and `1` standing for `X` and
`q`.  This is the usual polynomial ring `ℚ[X,q]`.
-/

noncomputable def factorX : MvPolynomial (Fin 2) ℚ := MvPolynomial.X 0

noncomputable def factorQ : MvPolynomial (Fin 2) ℚ := MvPolynomial.X 1

noncomputable def fixedTotalFactorProduct (ell : ℕ) (μ : Fin ell → ℕ) : MvPolynomial (Fin 2) ℚ :=
  ∏ i, (1 + factorX * factorQ ^ μ i)

noncomputable def fixedTotalFactorProducts (ell N : ℕ) : Set (MvPolynomial (Fin 2) ℚ) :=
  {p | ∃ μ : Fin ell → ℕ, (∑ i, μ i) = N ∧ p = fixedTotalFactorProduct ell μ}

noncomputable def fixedTotalFactorProductSpan (ell N : ℕ) : Submodule ℚ (MvPolynomial (Fin 2) ℚ) :=
  Submodule.span ℚ (fixedTotalFactorProducts ell N)

/-- The dimension `D(ell,N)` from Claim 22086. -/
noncomputable def fixedTotalFactorProductSpanDimension (ell N : ℕ) : ℕ :=
  Module.finrank ℚ (fixedTotalFactorProductSpan ell N)

/-- Claim 22088: the stable nine-factor dimension formula. -/
def stableNineFactorDimensionFormula : Prop :=
  ∀ N : ℕ, 7 ≤ N → fixedTotalFactorProductSpanDimension 9 N = 4 * N - 15

/-- Claim 22143: the stable twelve-factor dimension formula. -/
def stableTwelveFactorDimensionFormula : Prop :=
  ∀ N : ℕ, 10 ≤ N →
    fixedTotalFactorProductSpanDimension 12 N = 5 * N + N / 2 - 29

end MathlibPlus.Open.Research.FormalizationBatch
