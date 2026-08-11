import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace MathlibPlus.Algebra.Claim29002

/-- Claim 29002: if `a = floor(r/2)` and `b = ceil(r/2)`, the balanced
three-branch grade is `r(r-1) - ab`, equivalently
`r(r-1) - floor(r^2/4)`. Natural division represents the displayed floors. -/
theorem balanced_split_grade (r : ℕ) :
    let a := r / 2
    let b := (r + 1) / 2
    let q := r.choose 2 + a.choose 2 + b.choose 2
    q = r * (r - 1) - a * b ∧
      r * (r - 1) - a * b = r * (r - 1) - r ^ 2 / 4 := by
  dsimp
  have hchoose2 : ∀ x : ℕ, 2 * x.choose 2 = x * (x - 1) := by
    intro x
    rw [Nat.choose_two_right]
    simpa [Nat.mul_comm] using
      (Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self x))
  rcases Nat.mod_two_eq_zero_or_one r with hmod | hmod
  · obtain ⟨k, hr⟩ : ∃ k, r = 2 * k := by
      refine ⟨r / 2, ?_⟩
      omega
    rw [hr]
    have hdiv1 : (2 * k) / 2 = k := by omega
    have hdiv2 : (2 * k + 1) / 2 = k := by omega
    have hdiv4 : (2 * k) ^ 2 / 4 = k ^ 2 := by
      rw [show (2 * k) ^ 2 = 4 * k ^ 2 by ring]
      exact Nat.mul_div_cancel_left (k ^ 2) (by norm_num)
    simp only [hdiv1, hdiv2, hdiv4]
    constructor
    · apply Nat.eq_of_mul_eq_mul_left (n := 2) (by norm_num)
      rw [Nat.mul_add, Nat.mul_add]
      simp_rw [hchoose2]
      have hdist :
          2 * ((2 * k) * (2 * k - 1) - k * k) =
            2 * ((2 * k) * (2 * k - 1)) - 2 * (k * k) := by
        rw [Nat.mul_sub_left_distrib]
      rw [hdist]
      have hA0 : (2 * k) * (2 * k - 1) =
          (2 * k) * (2 * k) - (2 * k) * 1 := by
        rw [Nat.mul_sub_left_distrib]
      rw [hA0]
      have hsub : k * k - k + k = k * k :=
        Nat.sub_add_cancel (Nat.le_mul_self k)
      have h1 : k * (k - 1) = k * k - k := by
        rw [Nat.mul_sub_left_distrib]
        simp
      simp_rw [h1]
      have hmul : (2 * k) * k = 2 * (k * k) := by ring
      have hsq : (2 * k) * (2 * k) = 4 * (k * k) := by ring
      clear hdiv1 hdiv2 hdiv4 hmod hr r hchoose2
      omega
    · simp [pow_two]
  · obtain ⟨k, hr⟩ : ∃ k, r = 2 * k + 1 := by
      refine ⟨r / 2, ?_⟩
      omega
    rw [hr]
    have hdiv1 : (2 * k + 1) / 2 = k := by omega
    have hdiv2 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    have hdiv4 : (2 * k + 1) ^ 2 / 4 = k ^ 2 + k := by
      have hsq : (2 * k + 1) ^ 2 = 4 * (k ^ 2 + k) + 1 := by ring
      rw [hsq]
      calc
        (4 * (k ^ 2 + k) + 1) / 4 =
            (1 + 4 * (k ^ 2 + k)) / 4 := by rw [Nat.add_comm]
        _ = 1 / 4 + (k ^ 2 + k) := by
          simpa using (Nat.add_mul_div_left 1 (k ^ 2 + k) (by norm_num : 0 < 4))
        _ = k ^ 2 + k := by norm_num
    have hminus : 2 * k + 1 - 1 = 2 * k := by omega
    have hkp : k + 1 - 1 = k := by omega
    simp only [hdiv1, hdiv2, hdiv4, hminus]
    constructor
    · apply Nat.eq_of_mul_eq_mul_left (n := 2) (by norm_num)
      rw [Nat.mul_add, Nat.mul_add]
      simp_rw [hchoose2]
      rw [hminus, hkp]
      have hdist :
          2 * ((2 * k + 1) * (2 * k) - k * (k + 1)) =
            2 * ((2 * k + 1) * (2 * k)) - 2 * (k * (k + 1)) := by
        rw [Nat.mul_sub_left_distrib]
      rw [hdist]
      have hprod' : k * (k + 1) = k * k + k := by ring
      rw [hprod']
      have hsub : k * k - k + k = k * k :=
        Nat.sub_add_cancel (Nat.le_mul_self k)
      have h1 : k * (k - 1) = k * k - k := by
        rw [Nat.mul_sub_left_distrib]
        simp
      simp_rw [h1]
      have hmul : (2 * k) * k = 2 * (k * k) := by ring
      have hmul2 : (k + 1) * k = k * k + k := by ring
      have hA : (2 * k + 1) * (2 * k) = 4 * (k * k) + 2 * k := by ring
      have hB : (2 * k) * (k + 1) = 2 * (k * k) + 2 * k := by ring
      clear hdiv1 hdiv2 hdiv4 hminus hkp hmod hr r hchoose2
      omega
    · have hprod : k * (k + 1) = k * k + k := by ring
      rw [hprod]
      simp [pow_two]

end MathlibPlus.Algebra.Claim29002
