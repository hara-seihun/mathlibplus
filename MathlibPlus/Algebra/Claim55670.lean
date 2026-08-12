import Mathlib

namespace MathlibPlus.Algebra

/-- The support-five mass-three branch yields the Markov relation after
normalizing all rooted factors by a common invertible factor. -/
theorem supportFiveMarkov_claim55670
    {K : Type*} [CommRing K] [NoZeroDivisors K]
    (P Q A B C pInv : K)
    (hP : P * pInv = 1)
    (hadd : 2 * P + Q = A + B + C)
    (hmul : P ^ 2 * Q = A * B * C)
    (hnotone : A * pInv ≠ 1 ∧ B * pInv ≠ 1 ∧ C * pInv ≠ 1)
    (_hdistinct : A * pInv ≠ B * pInv ∧ A * pInv ≠ C * pInv ∧
      B * pInv ≠ C * pInv) :
    Q * pInv = (A * pInv) * (B * pInv) * (C * pInv) ∧
      A * pInv + B * pInv + C * pInv =
        2 + (A * pInv) * (B * pInv) * (C * pInv) ∧
      (A * pInv) * (B * pInv) ≠ 1 ∧
      (B * pInv) * (C * pInv) ≠ 1 ∧
      (A * pInv) * (C * pInv) ≠ 1 := by
  have hprod : Q * pInv = (A * pInv) * (B * pInv) * (C * pInv) := by
    calc
      Q * pInv = Q * pInv * (P * pInv) ^ 2 := by rw [hP]; ring
      _ = (P ^ 2 * Q) * pInv ^ 3 := by ring
      _ = (A * B * C) * pInv ^ 3 := by rw [hmul]
      _ = (A * pInv) * (B * pInv) * (C * pInv) := by ring
  have hmarkov : A * pInv + B * pInv + C * pInv =
      2 + (A * pInv) * (B * pInv) * (C * pInv) := by
    calc
      A * pInv + B * pInv + C * pInv = (A + B + C) * pInv := by ring
      _ = (2 * P + Q) * pInv := by rw [hadd]
      _ = 2 * (P * pInv) + Q * pInv := by ring
      _ = 2 + Q * pInv := by rw [hP]; ring
      _ = 2 + (A * pInv) * (B * pInv) * (C * pInv) := by rw [hprod]
  have no_pair_product {x y z : K} (hx : x ≠ 1) (hy : y ≠ 1)
      (hmark : x + y + z = 2 + x * y * z) : x * y ≠ 1 := by
    intro hxy
    have hsum : x + y = 2 := by
      calc
        x + y = (x + y + z) - z := by ring
        _ = (2 + x * y * z) - z := by rw [hmark]
        _ = 2 := by rw [hxy]; ring
    have hfactor : (x - 1) * (y - 1) = 0 := by
      calc
        (x - 1) * (y - 1) = x * y - x - y + 1 := by ring
        _ = 1 - x - y + 1 := by rw [hxy]
        _ = 2 - (x + y) := by ring
        _ = 0 := by rw [hsum]; ring
    rcases mul_eq_zero.mp hfactor with hx1 | hy1
    · exact hx (sub_eq_zero.mp hx1)
    · exact hy (sub_eq_zero.mp hy1)
  rcases hnotone with ⟨ha, hb, hc⟩
  exact ⟨hprod, hmarkov,
    @no_pair_product (A * pInv) (B * pInv) (C * pInv) ha hb hmarkov,
    @no_pair_product (B * pInv) (C * pInv) (A * pInv) hb hc (by
      simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
        using hmarkov),
    @no_pair_product (A * pInv) (C * pInv) (B * pInv) ha hc (by
      simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
        using hmarkov)⟩

end MathlibPlus.Algebra
