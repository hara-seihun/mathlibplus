import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0871

noncomputable section

abbrev BinaryPolynomial := MvPolynomial (Fin 2) ℚ

private def scalar (lam : ℚ) : BinaryPolynomial :=
  (algebraMap ℚ BinaryPolynomial) lam

private def binaryZ (lam : ℚ) (X Y : BinaryPolynomial) : BinaryPolynomial :=
  scalar lam * X - Y

private def firstSplitSeries
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

/-- Claim 29626: after the exact next-coefficient extraction from the
normalized cross-ratio identity, the common first-row factor is absent from
the tangent and all three binary-core divisibility channels follow. -/
def claim29626 : Prop :=
  ∀ (h : ℕ) (lam : ℚ)
    (A B D : PowerSeries BinaryPolynomial)
    (a b c d H X Y Z : BinaryPolynomial),
    firstSplitSeries h lam A B D a b c d H X Y Z →
      PowerSeries.coeff (2 * h + 1)
          (D * (PowerSeries.C (scalar lam) * A - B) -
            PowerSeries.C (scalar lam - 1) * A * B) = 0 ∧
      d * Z ^ 2 + (scalar lam - 1) *
          (a * Y ^ 2 - scalar lam * b * X ^ 2) = 0 ∧
      a * Y ^ 2 - scalar lam * b * X ^ 2 + c * Z ^ 2 = 0 ∧
      X ∣ a + c ∧
        Y ∣ scalar lam * c - b ∧
          Z ∣ scalar lam * a - b

end

end MathlibPlus.Open.ResearchFormalization.R0871
