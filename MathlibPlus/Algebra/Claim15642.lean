import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace MathlibPlus.Algebra.Claim15642

/-!
The two equal-radius conditions are stated with `Complex.normSq`; the second
branch is the canonical `Star ℂ` conjugation.
-/

/-- Equal distances from `0` and `1` determine a complex point up to
conjugation. -/
theorem equalRadiusConjugacy (a z : ℂ)
    (h₀ : Complex.normSq a = Complex.normSq z)
    (h₁ : Complex.normSq (a - 1) = Complex.normSq (z - 1)) :
    z = a ∨ z = star a := by
  have hreal : a.re = z.re := by
    norm_num [Complex.normSq_apply] at h₀ h₁
    nlinarith [h₀, h₁]
  have hreal_sq : a.re ^ 2 = z.re ^ 2 := by rw [hreal]
  have himsq : z.im ^ 2 = a.im ^ 2 := by
    norm_num [Complex.normSq_apply] at h₀
    nlinarith [h₀, hreal_sq]
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ himsq with him | him
  · left
    apply Complex.ext <;> simp [hreal, him]
  · right
    apply Complex.ext <;> simp [hreal, him]

end MathlibPlus.Algebra.Claim15642
