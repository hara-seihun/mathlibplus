import MathlibPlus.Analysis.CayleyRate

namespace MathlibPlus.Analysis.Claim14200

open MathlibPlus.Analysis.CayleyRate

/-- The exact exponential-modulus identity and strict boundary-rate inequality
from admitted claim 14200.  The source's separate phrase "right-of-line zero"
is not given a canonical Lean predicate here; the displayed rate inequality is
formalized with the source's explicit `β < 1` and nonzero-`ρ` hypotheses. -/
theorem stripShellBoundaryRate (β γ x : ℝ) (hβ : β < 1) (hx : 0 < x)
    (hρ : (β : ℂ) + (γ : ℂ) * Complex.I ≠ 0) :
    let ρ : ℂ := (β : ℂ) + (γ : ℂ) * Complex.I
    let wρ : ℂ := 1 - 1 / ρ
    ‖Complex.exp ((x : ℂ) / wρ)‖ =
        Real.exp (x * Complex.re (1 / wρ)) ∧
      ‖Complex.exp ((x : ℂ) / wρ)‖ < Real.exp x := by
  dsimp
  have hrate := exactPositiveAxisRateFormula β γ hβ hρ
  have hRe : Complex.re (1 / (1 - 1 / ((β : ℂ) + (γ : ℂ) * Complex.I))) < 1 :=
    hrate.2.2.2
  have hscalar :
      Complex.re ((x : ℂ) / (1 - 1 / ((β : ℂ) + (γ : ℂ) * Complex.I))) =
        x * Complex.re (1 / (1 - 1 / ((β : ℂ) + (γ : ℂ) * Complex.I))) := by
    rw [div_eq_mul_inv]
    simp [Complex.mul_re]
  constructor
  · rw [Complex.norm_exp, hscalar]
  · rw [Complex.norm_exp, hscalar]
    apply (Real.exp_lt_exp).2
    simpa using mul_lt_mul_of_pos_left hRe hx

end MathlibPlus.Analysis.Claim14200
