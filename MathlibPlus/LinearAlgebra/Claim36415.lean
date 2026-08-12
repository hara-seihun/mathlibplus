import MathlibPlus.Basic

namespace MathlibPlus.LinearAlgebra.Claim36415

/-!
The source names `w_m`, `v`, and the patch unit graph without defining their
ambient lattice or graph interfaces.  The formalization keeps the exact
unit-vector/inner-product hypotheses needed by the displayed norm identity,
and proves the stated integer quadratic consequence without silently choosing a
particular lattice or graph encoding.
-/

/-- The squared-norm calculation underlying the lattice patch. -/
theorem squaredNorm_formula
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p q ρ : ℝ) (w v : E)
    (hw : ‖w‖ ^ 2 = 1) (hv : ‖v‖ ^ 2 = 1)
    (hinner : inner ℝ w v = ρ) :
    ‖p • w + q • v‖ ^ 2 = p ^ 2 + q ^ 2 + 2 * ρ * p * q := by
  rw [norm_add_sq_real]
  rw [norm_smul, norm_smul]
  rw [real_inner_smul_left, real_inner_smul_right]
  rw [hinner]
  simp only [mul_pow, Real.norm_eq_abs, sq_abs]
  rw [hw, hv]
  ring

/-- With both integer coordinates nonzero, the quadratic form is strictly larger
than one. -/
theorem integer_quadratic_gt_one_of_ne
    (p q : ℤ) (ρ : ℝ) (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1 / 2)
    (hp : p ≠ 0) (hq : q ≠ 0) :
    (1 : ℝ) < (p : ℝ) ^ 2 + (q : ℝ) ^ 2 +
      2 * ρ * (p : ℝ) * (q : ℝ) := by
  have hpabs : (1 : ℝ) ≤ |(p : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hp
  have hqabs : (1 : ℝ) ≤ |(q : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hq
  have hp_sqabs : |(p : ℝ)| ^ 2 = (p : ℝ) ^ 2 := sq_abs _
  have hq_sqabs : |(q : ℝ)| ^ 2 = (q : ℝ) ^ 2 := sq_abs _
  have hp2 : (1 : ℝ) ≤ (p : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (|(p : ℝ)| - 1), hp_sqabs]
  have hq2 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (|(q : ℝ)| - 1), hq_sqabs]
  by_cases hprod : 0 < (p : ℝ) * (q : ℝ)
  · have hcross : 0 < 2 * ρ * (p : ℝ) * (q : ℝ) := by
      have hρprod : 0 < ρ * ((p : ℝ) * (q : ℝ)) :=
        mul_pos hρ₀ hprod
      nlinarith
    nlinarith
  · have hprod' : (p : ℝ) * (q : ℝ) < 0 := by
      have hne : (p : ℝ) * (q : ℝ) ≠ 0 := by
        exact mul_ne_zero (by exact_mod_cast hp) (by exact_mod_cast hq)
      exact lt_of_le_of_ne (le_of_not_gt hprod) hne
    have h2ρ : 2 * ρ < (1 : ℝ) := by nlinarith
    have hρmul : (p : ℝ) * (q : ℝ) <
        2 * ρ * (p : ℝ) * (q : ℝ) := by
      have h := mul_lt_mul_of_neg_right h2ρ hprod'
      nlinarith
    have habsprod : |(p : ℝ)| * |(q : ℝ)| =
        -((p : ℝ) * (q : ℝ)) := by
      rw [← abs_mul, abs_of_neg hprod']
    have hprodabs : (1 : ℝ) ≤ |(p : ℝ)| * |(q : ℝ)| := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hpabs)
        (sub_nonneg.mpr hqabs)]
    have hsum : (1 : ℝ) ≤ (p : ℝ) ^ 2 + (q : ℝ) ^ 2 +
        (p : ℝ) * (q : ℝ) := by
      nlinarith [sq_nonneg (|(p : ℝ)| - |(q : ℝ)|),
        hp_sqabs, hq_sqabs, habsprod, hprodabs]
    nlinarith

/-- The integer quadratic form in claim 36415 has the asserted lower bound. -/
theorem integer_quadratic_ge_one
    (p q : ℤ) (ρ : ℝ) (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1 / 2)
    (hpq : p ≠ 0 ∨ q ≠ 0) :
    (1 : ℝ) ≤ (p : ℝ) ^ 2 + (q : ℝ) ^ 2 +
      2 * ρ * (p : ℝ) * (q : ℝ) := by
  by_cases hp : p = 0
  · subst p
    have hq : q ≠ 0 := hpq.resolve_left (by simp)
    have hqabs : (1 : ℝ) ≤ |(q : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hq
    have hq_sqabs : |(q : ℝ)| ^ 2 = (q : ℝ) ^ 2 := sq_abs _
    have hq2 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (|(q : ℝ)| - 1), hq_sqabs]
    simpa using hq2
  · by_cases hq : q = 0
    · subst q
      have hpabs : (1 : ℝ) ≤ |(p : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs hp
      have hp_sqabs : |(p : ℝ)| ^ 2 = (p : ℝ) ^ 2 := sq_abs _
      have hp2 : (1 : ℝ) ≤ (p : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (|(p : ℝ)| - 1), hp_sqabs]
      simpa using hp2
    · have hpabs : (1 : ℝ) ≤ |(p : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs hp
      have hqabs : (1 : ℝ) ≤ |(q : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs hq
      have hp_sqabs : |(p : ℝ)| ^ 2 = (p : ℝ) ^ 2 := sq_abs _
      have hq_sqabs : |(q : ℝ)| ^ 2 = (q : ℝ) ^ 2 := sq_abs _
      have hp2 : (1 : ℝ) ≤ (p : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (|(p : ℝ)| - 1), hp_sqabs]
      have hq2 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (|(q : ℝ)| - 1), hq_sqabs]
      by_cases hprod : 0 < (p : ℝ) * (q : ℝ)
      · have hcross : 0 ≤ 2 * ρ * (p : ℝ) * (q : ℝ) := by
          have hρprod : 0 < ρ * ((p : ℝ) * (q : ℝ)) :=
            mul_pos hρ₀ hprod
          nlinarith
        nlinarith
      · have hprod' : (p : ℝ) * (q : ℝ) < 0 := by
          have hne : (p : ℝ) * (q : ℝ) ≠ 0 := by
            exact mul_ne_zero (by exact_mod_cast hp) (by exact_mod_cast hq)
          exact lt_of_le_of_ne (le_of_not_gt hprod) hne
        have h2ρ : 2 * ρ < (1 : ℝ) := by nlinarith
        have hρmul : (p : ℝ) * (q : ℝ) <
            2 * ρ * (p : ℝ) * (q : ℝ) := by
          have h := mul_lt_mul_of_neg_right h2ρ hprod'
          nlinarith
        have habsprod : |(p : ℝ)| * |(q : ℝ)| =
            -((p : ℝ) * (q : ℝ)) := by
          rw [← abs_mul, abs_of_neg hprod']
        have hprodabs : (1 : ℝ) ≤ |(p : ℝ)| * |(q : ℝ)| := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hpabs)
            (sub_nonneg.mpr hqabs)]
        have hp_sqabs : |(p : ℝ)| ^ 2 = (p : ℝ) ^ 2 := sq_abs _
        have hq_sqabs : |(q : ℝ)| ^ 2 = (q : ℝ) ^ 2 := sq_abs _
        have hsum : (1 : ℝ) ≤ (p : ℝ) ^ 2 + (q : ℝ) ^ 2 +
            (p : ℝ) * (q : ℝ) := by
          nlinarith [sq_nonneg (|(p : ℝ)| - |(q : ℝ)|),
            hp_sqabs, hq_sqabs, habsprod, hprodabs]
        nlinarith

/-- Equality in the lower bound occurs only on a signed coordinate vector. -/
theorem integer_quadratic_eq_one_iff
    (p q : ℤ) (ρ : ℝ) (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1 / 2)
    (hpq : p ≠ 0 ∨ q ≠ 0) :
    (p : ℝ) ^ 2 + (q : ℝ) ^ 2 +
        2 * ρ * (p : ℝ) * (q : ℝ) = 1 ↔
      ((p = 1 ∨ p = -1) ∧ q = 0) ∨
        (p = 0 ∧ (q = 1 ∨ q = -1)) := by
  constructor
  · intro hEq
    by_cases hp : p = 0
    · right
      refine ⟨hp, ?_⟩
      have hq : q ≠ 0 := hpq.resolve_left (by simp [hp])
      have hqeq : (q : ℝ) ^ 2 = 1 := by
        simpa [hp] using hEq
      have hqcast : (q : ℝ) = 1 ∨ (q : ℝ) = -1 :=
        (sq_eq_one_iff).mp hqeq
      exact hqcast.imp (fun h => by exact_mod_cast h)
        (fun h => by exact_mod_cast h)
    · by_cases hq : q = 0
      · left
        refine ⟨?_, hq⟩
        have hpeq : (p : ℝ) ^ 2 = 1 := by
          simpa [hq] using hEq
        have hpcast : (p : ℝ) = 1 ∨ (p : ℝ) = -1 :=
          (sq_eq_one_iff).mp hpeq
        exact hpcast.imp (fun h => by exact_mod_cast h)
          (fun h => by exact_mod_cast h)
      · exfalso
        have hgt := integer_quadratic_gt_one_of_ne p q ρ hρ₀ hρ₁ hp hq
        nlinarith
  · rintro (⟨hp, hq⟩ | ⟨hp, hq⟩)
    · rcases hp with rfl | rfl <;> subst q <;> norm_num
    · rcases hq with rfl | rfl <;> subst p <;> norm_num

end MathlibPlus.LinearAlgebra.Claim36415
