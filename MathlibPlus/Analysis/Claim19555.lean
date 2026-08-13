import Mathlib

namespace MathlibPlus.Analysis.Claim19555

/-- The exact three-root description and first-barrier placement from claim 19555.

The local definitions keep the statement self-contained while retaining the
witness polynomial and both radical roots exactly. -/
theorem exact_roots_claim19555 :
    let h : ℝ → ℝ := fun q => (q - 2) * (8 * q ^ 2 - 50 * q + 7) / 2
    let rhoMinus : ℝ := (25 - Real.sqrt 569) / 8
    let rho : ℝ := (25 + Real.sqrt 569) / 8
    (∀ q, h q = 0 ↔ q = 2 ∨ q = rhoMinus ∨ q = rho) ∧
      rhoMinus < 2 ∧ 2 < rho := by
  dsimp
  have hs : (Real.sqrt (569 : ℝ)) ^ 2 = 569 :=
    Real.sq_sqrt (by norm_num)
  have hs_nonneg : 0 ≤ Real.sqrt (569 : ℝ) := Real.sqrt_nonneg _
  have hs_pos : 0 < Real.sqrt (569 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hfactor (q : ℝ) :
      8 * q ^ 2 - 50 * q + 7 =
        8 * (q - (25 - Real.sqrt 569) / 8) *
          (q - (25 + Real.sqrt 569) / 8) := by
    nlinarith [hs]
  constructor
  · intro q
    constructor
    · intro hq
      have hprod : (q - 2) * (8 * q ^ 2 - 50 * q + 7) = 0 := by
        nlinarith [hq]
      rcases mul_eq_zero.mp hprod with hlinear | hquad
      · left
        linarith
      · have hroots :
            (q - (25 - Real.sqrt 569) / 8) *
                (q - (25 + Real.sqrt 569) / 8) = 0 := by
          rw [hfactor] at hquad
          nlinarith [hquad]
        rcases mul_eq_zero.mp hroots with hminus | hplus
        · right
          left
          linarith
        · right
          right
          linarith
    · rintro (rfl | rfl | rfl)
      · norm_num
      · nlinarith [hs]
      · nlinarith [hs]
  · constructor
    · nlinarith [hs, hs_nonneg]
    · nlinarith [hs_pos]

end MathlibPlus.Analysis.Claim19555
