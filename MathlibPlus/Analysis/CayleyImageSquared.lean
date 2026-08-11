import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace MathlibPlus.Analysis.CayleyImageSquared

/-- Claim 14196: the squared modulus of the Cayley image of a strip point. -/
theorem cayleyImage_normSq (β γ : ℝ) (hβ : 0 < β) (hβ1 : β < 1) :
    let ρ : ℂ := (β : ℂ) + (γ : ℂ) * Complex.I
    let wρ : ℂ := 1 - 1 / ρ
    Complex.normSq wρ = ((β - 1)^2 + γ^2) / (β^2 + γ^2) := by
  dsimp
  have hρ : (β : ℂ) + (γ : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    norm_num at hr hi
    linarith
  have hden : β^2 + γ^2 ≠ 0 := by
    intro h
    have hβ0 : β = 0 := by
      nlinarith [sq_nonneg β, sq_nonneg γ]
    linarith
  simp [Complex.normSq_apply, Complex.div_re, Complex.div_im, hρ, hden]
  field_simp [hden]
  ring

end MathlibPlus.Analysis.CayleyImageSquared
