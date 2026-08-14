import MathlibPlus.Basic

open Set
open scoped Interval

noncomputable section

namespace MathlibPlus.Analysis.Mellin

/--
Claim 17797: expanding the positive-cell Mellin amplitude and changing variables
by `x = 1 / y` gives its reciprocal-cell integral.  The local `I` expands the
source's `I_n`; powers on positive real bases use Mathlib's principal
`Complex.cpow` convention.
-/
theorem reciprocalSubstitution_claim17797 (n : ℕ) (hn : 1 ≤ n) (s : ℂ) :
    (let I : ℂ → ℂ := fun z =>
      ∫ x in (n : ℝ)..(n + 1 : ℝ),
        ((x - (n : ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-z - 1)
     I (1 - s) =
      ∫ y in (1 / ((n + 1 : ℕ) : ℝ))..(1 / (n : ℝ)),
        ((1 - (n : ℝ) * y : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1)) := by
  let a : ℝ := 1 / ((n + 1 : ℕ) : ℝ)
  let b : ℝ := 1 / (n : ℝ)
  let f : ℝ → ℝ := fun y => y⁻¹
  let g : ℝ → ℂ := fun x =>
    ((x - (n : ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-(1 - s) - 1)
  have hn0 : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hab : a ≤ b := by
    dsimp [a, b]
    apply one_div_le_one_div_of_le
    · exact hn0
    · norm_num
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hpos : ∀ x ∈ f '' Set.uIcc a b, 0 < x := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    have hy' : 0 < y := by
      rw [Set.uIcc_of_le hab] at hy
      exact lt_of_lt_of_le ha hy.1
    exact inv_pos.mpr hy'
  have hderiv : ∀ y ∈ Set.uIcc a b,
      HasDerivAt f (-1 / y ^ 2) y := by
    intro y hy
    dsimp [f]
    change HasDerivAt (fun y : ℝ => (id y)⁻¹) (-1 / y ^ 2) y
    exact (hasDerivAt_id y).inv (ne_of_gt (lt_of_lt_of_le ha (by
      rw [Set.uIcc_of_le hab] at hy
      exact hy.1)))
  have hderiv_cont : ContinuousOn (fun y : ℝ => -1 / y ^ 2) (Set.uIcc a b) := by
    apply ContinuousOn.div continuousOn_const.neg (continuousOn_id.pow 2)
    intro y hy
    exact ne_of_gt (sq_pos_of_pos (lt_of_lt_of_le ha (by
      rw [Set.uIcc_of_le hab] at hy
      exact hy.1)))
  have hg : ContinuousOn g (f '' Set.uIcc a b) := by
    apply ContinuousOn.mul
    · exact (Complex.continuous_ofReal.comp (continuous_id.sub continuous_const)).continuousOn
    · intro x hx
      exact (Complex.continuousAt_ofReal_cpow_const x _
        (Or.inr (ne_of_gt (hpos x hx)))).continuousWithinAt
  have hchange := intervalIntegral.integral_deriv_smul_comp' hderiv hderiv_cont hg
  dsimp [a, b, f, g] at hchange ⊢
  have hpoint (y : ℝ) (hy : 0 < y) :
      ((-1 / y ^ 2 : ℝ) : ℂ) *
          (((y⁻¹ - (n : ℝ) : ℝ) : ℂ) *
            ((y⁻¹ : ℝ) : ℂ) ^ (-(1 - s) - 1)) =
        -(((1 - (n : ℝ) * y : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1)) := by
    rw [Complex.ofReal_inv]
    have hexp : -(1 - s) - 1 = s - 2 := by ring
    rw [hexp]
    rw [Complex.inv_cpow_ofReal_nonneg hy.le]
    rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr hy.ne')]
    rw [inv_div]
    have hpow : (y : ℂ) ^ (-s - 1) =
        (y : ℂ) ^ (-s) * (y : ℂ)⁻¹ := by
      rw [show -s - 1 = (-s) + (-1) by ring,
        Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hy.ne'),
        Complex.cpow_neg_one]
    rw [hpow]
    simp only [div_eq_mul_inv]
    rw [← Complex.cpow_neg]
    norm_num [hy.ne']
    field_simp [hy.ne']
  have hleft :
      (∫ y : ℝ in 1 / ((n + 1 : ℕ) : ℝ)..1 / (n : ℝ),
        ((-1 / y ^ 2 : ℝ) : ℂ) *
          (((y⁻¹ - (n : ℝ) : ℝ) : ℂ) *
            ((y⁻¹ : ℝ) : ℂ) ^ (-(1 - s) - 1))) =
        -(∫ y : ℝ in 1 / ((n + 1 : ℕ) : ℝ)..1 / (n : ℝ),
          ((1 - (n : ℝ) * y : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1) ) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro y hy
    have hypos : 0 < y := by
      rw [Set.uIcc_of_le hab] at hy
      exact lt_of_lt_of_le ha hy.1
    exact hpoint y hypos
  have hna : (1 / ((n + 1 : ℕ) : ℝ))⁻¹ = (n + 1 : ℝ) := by
    field_simp
    norm_num
  have hnb : (1 / (n : ℝ))⁻¹ = (n : ℝ) := by
    field_simp [hn0.ne']
  simp only [hna, hnb] at hchange
  have hrev :
      (∫ x : ℝ in (n + 1 : ℝ)..(n : ℝ),
        ((x - (n : ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-(1 - s) - 1)) =
        -(∫ x : ℝ in (n : ℝ)..(n + 1 : ℝ),
          ((x - (n : ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-(1 - s) - 1)) := by
    exact intervalIntegral.integral_symm (n : ℝ) (n + 1 : ℝ)
  rw [hrev] at hchange
  have hneg := hleft.symm.trans hchange
  exact (neg_injective hneg).symm

end MathlibPlus.Analysis.Mellin
