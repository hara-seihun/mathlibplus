import MathlibPlus.Basic

namespace MathlibPlus.Algebra

/-!
Formalization of admitted claim 11976 (O-0209).  This records the exact
endpoint-root witness and the linear real homotopy; it does not assert the
packet's separate discriminant or sheet-continuation analysis.
-/

/-- The displayed rational cubic homotopy has exactly the displayed endpoint roots. -/
theorem rationalCubicHomotopy :
    let F₀ : ℂ → ℂ := fun x => (x ^ 2 + 1) * (x - 3)
    let F₁ : ℂ → ℂ := fun x => (x + 2) * (x - 1) * (x - (3 / 2))
    let F : ℝ → ℂ → ℂ := fun s x =>
      (1 - (s : ℂ)) * F₀ x + (s : ℂ) * F₁ x
    F 0 = F₀ ∧ F 1 = F₁ ∧
      (∀ x : ℂ, F₀ x = 0 ↔
        x = Complex.I ∨ x = -Complex.I ∨ x = 3) ∧
      (∀ x : ℂ, F₁ x = 0 ↔
        x = -2 ∨ x = 1 ∨ x = (3 / 2 : ℂ)) := by
  dsimp
  constructor
  · ext x
    norm_num
  constructor
  · ext x
    norm_num
  constructor
  · intro x
    constructor
    · intro hx
      have hfac : (x - Complex.I) * (x + Complex.I) * (x - 3) = 0 := by
        have hi2 : (Complex.I : ℂ) ^ 2 = -1 := by
          norm_num [pow_two, Complex.I_mul_I]
        have hquad : (x - Complex.I) * (x + Complex.I) = x ^ 2 + 1 := by
          calc
            (x - Complex.I) * (x + Complex.I) = x ^ 2 - Complex.I ^ 2 := by ring
            _ = x ^ 2 + 1 := by rw [hi2]; ring
        calc
          (x - Complex.I) * (x + Complex.I) * (x - 3) =
              (x ^ 2 + 1) * (x - 3) := by rw [hquad]
          _ = 0 := hx
      rcases mul_eq_zero.mp hfac with hquad | hthree
      · rcases mul_eq_zero.mp hquad with hi | hmi
        · left
          exact sub_eq_zero.mp hi
        · right
          left
          exact add_eq_zero_iff_eq_neg.mp hmi
      · right
        right
        exact sub_eq_zero.mp hthree
    · rintro (rfl | rfl | rfl) <;> norm_num [Complex.I_mul_I]
  · intro x
    constructor
    · intro hx
      rcases mul_eq_zero.mp hx with hleft | hright
      · rcases mul_eq_zero.mp hleft with hneg2 | hone
        · left
          exact add_eq_zero_iff_eq_neg.mp hneg2
        · right
          left
          exact sub_eq_zero.mp hone
      · right
        right
        exact sub_eq_zero.mp hright
    · rintro (rfl | rfl | rfl) <;> norm_num

end MathlibPlus.Algebra
