import MathlibPlus.Open.ResearchFormalization.R0871Claim29626

namespace MathlibPlus.Open.ResearchFormalization.R0871

noncomputable section

private def scalar29622 (lam : ℚ) : BinaryPolynomial :=
  (algebraMap ℚ BinaryPolynomial) lam

private def firstSplitSeries29622
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
    PowerSeries.coeff h D = (scalar29622 lam - 1) * H * X * Y ∧
    PowerSeries.coeff (h + 1) A = a ∧
    PowerSeries.coeff (h + 1) B = b ∧
    PowerSeries.coeff (h + 1) D = d ∧
    Z = scalar29622 lam * X - Y ∧
    d = (scalar29622 lam - 1) * c ∧
    D * (PowerSeries.C (scalar29622 lam) * A - B) =
      PowerSeries.C (scalar29622 lam - 1) * A * B

/-- Claim 29622: the exact next-row coefficient extraction for the
all-distinct Record 2 first split, including its diagonal tangent syzygy. -/
def claim29622_nextRowTangent : Prop :=
  ∀ (h : ℕ) (lam : ℚ)
    (A B D : PowerSeries BinaryPolynomial)
    (a b c d H X Y Z : BinaryPolynomial),
    firstSplitSeries29622 h lam A B D a b c d H X Y Z →
      PowerSeries.coeff (2 * h + 1)
          (D * (PowerSeries.C (scalar29622 lam) * A - B) -
            PowerSeries.C (scalar29622 lam - 1) * A * B) = 0 ∧
      d * Z ^ 2 + (scalar29622 lam - 1) *
          (a * Y ^ 2 - scalar29622 lam * b * X ^ 2) = 0 ∧
      a * Y ^ 2 - scalar29622 lam * b * X ^ 2 + c * Z ^ 2 = 0

end

end MathlibPlus.Open.ResearchFormalization.R0871
