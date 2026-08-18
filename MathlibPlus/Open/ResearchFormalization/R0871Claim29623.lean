import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0871Claim29623

noncomputable section

abbrev BinaryPolynomial := MvPolynomial (Fin 2) ℚ

def scalar (lam : ℚ) : BinaryPolynomial :=
  (algebraMap ℚ BinaryPolynomial) lam

def firstSplitContext
    (h : ℕ) (lam : ℚ)
    (A B D : PowerSeries BinaryPolynomial)
    (a b c d H X Y Z : BinaryPolynomial) : Prop :=
  h > 0 ∧
    lam ≠ 0 ∧ lam ≠ 1 ∧
    H ≠ 0 ∧ X ≠ 0 ∧ Y ≠ 0 ∧ Z ≠ 0 ∧
    IsCoprime X Y ∧ IsCoprime X Z ∧ IsCoprime Y Z ∧
    (∀ k < h, PowerSeries.coeff k A = 0) ∧
    (∀ k < h, PowerSeries.coeff k B = 0) ∧
    (∀ k < h, PowerSeries.coeff k D = 0) ∧
    PowerSeries.coeff h A = H * X * Z ∧
    PowerSeries.coeff h B = H * Y * Z ∧
    PowerSeries.coeff h D = (scalar lam - 1) * H * X * Y ∧
    PowerSeries.coeff (h + 1) A = a ∧
    PowerSeries.coeff (h + 1) B = b ∧
    PowerSeries.coeff (h + 1) D = d ∧
    Z = scalar lam * X - Y ∧
    d = (scalar lam - 1) * c ∧
    D * (PowerSeries.C (scalar lam) * A - B) =
      PowerSeries.C (scalar lam - 1) * A * B

def tangentEquation
    (lam : ℚ) (X Y Z a b c : BinaryPolynomial) : Prop :=
  a * Y ^ 2 - scalar lam * b * X ^ 2 + c * Z ^ 2 = 0

/-- Claim 29623: in the exact first-split power-series context, the tangent
quadratic syzygy forces all three prescribed binary-core divisibilities. -/
def claim29623 : Prop :=
  ∀ (h : ℕ) (lam : ℚ)
    (A B D : PowerSeries BinaryPolynomial)
    (a b c d H X Y Z : BinaryPolynomial),
    firstSplitContext h lam A B D a b c d H X Y Z →
      tangentEquation lam X Y Z a b c →
      X ∣ a + c ∧
        Y ∣ scalar lam * c - b ∧
          Z ∣ scalar lam * a - b

end

end MathlibPlus.Open.ResearchFormalization.R0871Claim29623
