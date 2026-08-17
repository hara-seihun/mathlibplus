import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0500Claim25920

noncomputable section

private def qVar : Polynomial ℚ := Polynomial.X

private def totalExponent (mu : Fin 4 → ℕ) : ℕ :=
  ∑ i : Fin 4, mu i

private def singletonPolynomial (mu : Fin 4 → ℕ) : Polynomial ℚ :=
  ∑ i : Fin 4, qVar ^ mu i

private def fourFactorProduct (mu : Fin 4 → ℕ) : Polynomial (Polynomial ℚ) :=
  ∏ i : Fin 4,
    ((1 : Polynomial (Polynomial ℚ)) +
      (Polynomial.X : Polynomial (Polynomial ℚ)) *
        Polynomial.C (qVar ^ mu i))

private def fixedTotalProductSpan (N : ℕ) :
    Submodule ℚ (Polynomial (Polynomial ℚ)) :=
  Submodule.span ℚ
    {P | ∃ mu : Fin 4 → ℕ,
      totalExponent mu = N ∧ P = fourFactorProduct mu}

private def fourFactorDimension (N : ℕ) : ℕ :=
  Module.finrank ℚ (fixedTotalProductSpan N)

private def mu0 : Fin 4 → ℕ := ![0, 0, 0, 0]
private def mu1 : Fin 4 → ℕ := ![1, 0, 0, 0]
private def mu20 : Fin 4 → ℕ := ![2, 0, 0, 0]
private def mu21 : Fin 4 → ℕ := ![1, 1, 0, 0]
private def mu30 : Fin 4 → ℕ := ![3, 0, 0, 0]
private def mu31 : Fin 4 → ℕ := ![2, 1, 0, 0]
private def mu32 : Fin 4 → ℕ := ![1, 1, 1, 0]

private def displayedRows0 : Fin 1 → Polynomial ℚ :=
  fun _ => singletonPolynomial mu0

private def displayedRows1 : Fin 1 → Polynomial ℚ :=
  fun _ => singletonPolynomial mu1

private def displayedRows2 : Fin 2 → Polynomial ℚ
  | 0 => singletonPolynomial mu20
  | 1 => singletonPolynomial mu21

private def displayedRows3 : Fin 3 → Polynomial ℚ
  | 0 => singletonPolynomial mu30
  | 1 => singletonPolynomial mu31
  | 2 => singletonPolynomial mu32

/-- The four-factor fixed-total product span and the selected displayed
singleton rows for totals zero through three. -/
def claim25920 : Prop :=
  fourFactorDimension 0 = 1 ∧
    fourFactorDimension 1 = 1 ∧
    fourFactorDimension 2 = 2 ∧
    fourFactorDimension 3 = 3 ∧
    LinearIndependent ℚ displayedRows0 ∧
    LinearIndependent ℚ displayedRows1 ∧
    LinearIndependent ℚ displayedRows2 ∧
    LinearIndependent ℚ displayedRows3

end

end MathlibPlus.Open.ResearchFormalization.R0500Claim25920
