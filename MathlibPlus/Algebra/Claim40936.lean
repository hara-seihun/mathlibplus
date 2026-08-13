import Mathlib

namespace MathlibPlus.Algebra.Claim40936

/-- The exact third-collar arithmetic obstruction from claim 40936. -/
theorem thirdCoefficientObstruction_claim40936 :
    (174724 : ℤ) = 418 ^ 2 ∧
      (2935614 : ℤ) = 418 * 7023 ∧
      Int.ModEq 836 ((117977013 : ℤ) - 7023 ^ 2) 492 ∧
      ¬ ∃ u : ℤ, 2 * 418 * u + 7023 ^ 2 = 117977013 := by
  norm_num [Int.ModEq]
  intro u
  omega

/-- No integer square-root coefficient triple can satisfy the three displayed
necessary coefficient equations for the witness in claim 40936. -/
theorem no_squareRoot_coefficients_claim40936 :
    ¬ ∃ (r q u : ℤ),
      r ^ 2 = 174724 ∧
      r * q = 2935614 ∧
      2 * r * u + q ^ 2 = 117977013 := by
  rintro ⟨r, q, u, hr, hq, hu⟩
  have hsq : r ^ 2 = (418 : ℤ) ^ 2 := by
    norm_num at hr ⊢
    exact hr
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with hr' | hr'
  · subst r
    have hq' : q = 7023 := by omega
    subst q
    norm_num at hu
    omega
  · subst r
    have hq' : q = -7023 := by omega
    subst q
    norm_num at hu
    omega

end MathlibPlus.Algebra.Claim40936
