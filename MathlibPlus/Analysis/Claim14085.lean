import Mathlib

namespace MathlibPlus.Analysis.Claim14085

/-- Under the exponential interpretation of `p ^ (β - s)`, the Euler deformation
has the displayed vertical arithmetic progression of zeros.  The real part is
`β`, so the progression is off the critical line when `β > 1 / 2`. -/
theorem eulerDeformation_zeros_claim14085
    {p : ℕ} (hp : p.Prime) {β : ℝ} (hβ₁ : (1 : ℝ) / 2 < β) (_hβ₂ : β < 1) :
    ∀ k : ℤ,
      (riemannZeta ((β : ℂ) +
          ((2 * Real.pi * (k : ℝ) / Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I) *
        (1 - Complex.exp (((β : ℂ) -
          ((β : ℂ) +
            ((2 * Real.pi * (k : ℝ) / Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I)) *
          (Real.log (p : ℝ) : ℂ))) = 0) ∧
      (((β : ℂ) +
          ((2 * Real.pi * (k : ℝ) / Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I).re = β) ∧
      (((β : ℂ) +
          ((2 * Real.pi * (k : ℝ) / Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I).re ≠
        (1 : ℝ) / 2) := by
  have hp_one : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp.one_lt
  let ℓ : ℝ := Real.log (p : ℝ)
  have hℓ : ℓ ≠ 0 := by
    dsimp [ℓ]
    exact ne_of_gt (Real.log_pos hp_one)
  intro k
  change
    (riemannZeta ((β : ℂ) +
        ((2 * Real.pi * (k : ℝ) / ℓ : ℝ) : ℂ) * Complex.I) *
      (1 - Complex.exp (((β : ℂ) -
        ((β : ℂ) + ((2 * Real.pi * (k : ℝ) / ℓ : ℝ) : ℂ) * Complex.I)) *
        (ℓ : ℂ))) = 0) ∧
    (((β : ℂ) + ((2 * Real.pi * (k : ℝ) / ℓ : ℝ) : ℂ) * Complex.I).re = β) ∧
    (((β : ℂ) + ((2 * Real.pi * (k : ℝ) / ℓ : ℝ) : ℂ) * Complex.I).re ≠
      (1 : ℝ) / 2)
  have hexp : Complex.exp (((β : ℂ) -
      ((β : ℂ) +
        ((2 * Real.pi * (k : ℝ) / ℓ : ℝ) : ℂ) * Complex.I)) *
      (ℓ : ℂ)) = 1 := by
    rw [Complex.exp_eq_one_iff]
    refine ⟨-k, ?_⟩
    apply Complex.ext <;> simp
    field_simp [hℓ]
  refine ⟨by rw [hexp]; ring, ?_, ?_⟩
  · simp
  · simp
    norm_num
    exact hβ₁.ne'

end MathlibPlus.Analysis.Claim14085
