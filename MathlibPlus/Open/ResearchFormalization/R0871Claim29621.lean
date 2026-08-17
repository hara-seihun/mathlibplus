import Mathlib
import MathlibPlus.Open.ResearchFormalization.R0871Claim29626

namespace MathlibPlus.Open.ResearchFormalization.R0871Claim29621

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R0871

abbrev BinaryPolynomial29621 :=
  MvPolynomial (Fin 2) ℚ

def scalar29621 (lam : ℚ) : BinaryPolynomial29621 :=
  (algebraMap ℚ BinaryPolynomial29621) lam

def firstSplitAllDistinct29621
    (h : ℕ) (lam : ℚ)
    (A B D : PowerSeries BinaryPolynomial29621) : Prop :=
  h > 0 ∧
    lam ≠ 0 ∧ lam ≠ 1 ∧
    (∀ k < h, PowerSeries.coeff k A = 0) ∧
    (∀ k < h, PowerSeries.coeff k B = 0) ∧
    (∀ k < h, PowerSeries.coeff k D = 0) ∧
    PowerSeries.coeff h A ≠ 0 ∧
    PowerSeries.coeff h B ≠ 0 ∧
    PowerSeries.coeff h D ≠ 0 ∧
    PowerSeries.coeff h A ≠ PowerSeries.coeff h B ∧
    PowerSeries.coeff h A ≠ PowerSeries.coeff h D ∧
    PowerSeries.coeff h B ≠ PowerSeries.coeff h D ∧
    D * (PowerSeries.C (scalar29621 lam) * A - B) =
      PowerSeries.C (scalar29621 lam - 1) * A * B

/-- The all-distinct first split has the complete binary UFD normal form. -/
def claim29621 : Prop :=
  ∀ (h : ℕ) (lam : ℚ)
    (A B D : PowerSeries BinaryPolynomial29621),
    firstSplitAllDistinct29621 h lam A B D →
      ∃ H X Y Z : BinaryPolynomial29621,
        H ≠ 0 ∧ X ≠ 0 ∧ Y ≠ 0 ∧ Z ≠ 0 ∧
        IsCoprime X Y ∧ IsCoprime X Z ∧ IsCoprime Y Z ∧
        PowerSeries.coeff h A = H * X * Z ∧
        PowerSeries.coeff h B = H * Y * Z ∧
        PowerSeries.coeff h D =
          (scalar29621 lam - 1) * H * X * Y ∧
        Z = scalar29621 lam * X - Y

end

end MathlibPlus.Open.ResearchFormalization.R0871Claim29621
