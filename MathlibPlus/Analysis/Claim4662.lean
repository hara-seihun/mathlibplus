import Mathlib

namespace MathlibPlus.Analysis.ThetaShell

/-- Pointwise translated-shell identity for the theta kernel in admitted claim
4662. The factor with exponent `-1/2` is Lean's real `rpow`. -/
theorem thetaShellTranslationPointwise_4662 (m : ℕ) (hm : 1 ≤ m) (u : ℝ) :
    Real.exp (u / 2) *
        (4 * (Real.pi * (m : ℝ) ^ 2) ^ 2 * Real.exp (4 * u) -
          6 * (Real.pi * (m : ℝ) ^ 2) * Real.exp (2 * u)) *
        Real.exp (-(Real.pi * (m : ℝ) ^ 2) * Real.exp (2 * u)) =
      (m : ℝ) ^ (-(1 : ℝ) / 2) *
        (Real.exp ((u + Real.log (m : ℝ)) / 2) *
          (4 * Real.pi ^ 2 * Real.exp (4 * (u + Real.log (m : ℝ))) -
            6 * Real.pi * Real.exp (2 * (u + Real.log (m : ℝ)))) *
          Real.exp (-Real.pi * Real.exp (2 * (u + Real.log (m : ℝ))))) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hm)
  have hlog : Real.exp (Real.log (m : ℝ)) = (m : ℝ) :=
    Real.exp_log hm0
  have hpow2 : Real.exp (2 * Real.log (m : ℝ)) = (m : ℝ) ^ 2 := by
    calc
      Real.exp (2 * Real.log (m : ℝ)) =
          Real.exp (Real.log (m : ℝ)) ^ 2 := by
            simpa using (Real.exp_nat_mul (Real.log (m : ℝ)) 2)
      _ = (m : ℝ) ^ 2 := by rw [hlog]
  have hpow4 : Real.exp (4 * Real.log (m : ℝ)) = (m : ℝ) ^ 4 := by
    calc
      Real.exp (4 * Real.log (m : ℝ)) =
          Real.exp (Real.log (m : ℝ)) ^ 4 := by
            simpa using (Real.exp_nat_mul (Real.log (m : ℝ)) 4)
      _ = (m : ℝ) ^ 4 := by rw [hlog]
  have hhalf_sq : Real.exp (Real.log (m : ℝ) / 2) ^ 2 = (m : ℝ) := by
    rw [pow_two, ← Real.exp_add]
    convert hlog using 1 <;> ring_nf
  have hhalf : Real.exp (Real.log (m : ℝ) / 2) = Real.sqrt (m : ℝ) := by
    apply (sq_eq_sq₀ (le_of_lt (Real.exp_pos _)) (Real.sqrt_nonneg _)).mp
    rw [hhalf_sq, Real.sq_sqrt (le_of_lt hm0)]
  have hhalf_factor : (m : ℝ) ^ (-(1 : ℝ) / 2) *
      Real.exp (Real.log (m : ℝ) / 2) = 1 := by
    have hrpow : (m : ℝ) ^ (-(1 : ℝ) / 2) =
        ((m : ℝ) ^ ((1 : ℝ) / 2))⁻¹ := by
      convert Real.rpow_neg (le_of_lt hm0) ((1 : ℝ) / 2) using 1 <;> ring
    rw [hrpow, ← Real.sqrt_eq_rpow, hhalf]
    field_simp
  have hshift4 : Real.exp (4 * (u + Real.log (m : ℝ))) =
      Real.exp (4 * u) * (m : ℝ) ^ 4 := by
    rw [show 4 * (u + Real.log (m : ℝ)) = 4 * u + 4 * Real.log (m : ℝ) by ring,
      Real.exp_add, hpow4]
  have hshift2 : Real.exp (2 * (u + Real.log (m : ℝ))) =
      Real.exp (2 * u) * (m : ℝ) ^ 2 := by
    rw [show 2 * (u + Real.log (m : ℝ)) = 2 * u + 2 * Real.log (m : ℝ) by ring,
      Real.exp_add, hpow2]
  have hshift_half : Real.exp ((u + Real.log (m : ℝ)) / 2) =
      Real.exp (u / 2) * Real.exp (Real.log (m : ℝ) / 2) := by
    rw [show (u + Real.log (m : ℝ)) / 2 = u / 2 + Real.log (m : ℝ) / 2 by ring,
      Real.exp_add]
  have hcoef :
      4 * Real.pi ^ 2 * (Real.exp (4 * u) * (m : ℝ) ^ 4) -
          6 * Real.pi * (Real.exp (2 * u) * (m : ℝ) ^ 2) =
        4 * (Real.pi * (m : ℝ) ^ 2) ^ 2 * Real.exp (4 * u) -
          6 * (Real.pi * (m : ℝ) ^ 2) * Real.exp (2 * u) := by
    ring
  have houter :
      Real.exp (-Real.pi * (Real.exp (2 * u) * (m : ℝ) ^ 2)) =
        Real.exp (-(Real.pi * (m : ℝ) ^ 2) * Real.exp (2 * u)) := by
    congr 1
    ring
  rw [hshift_half, hshift4, hshift2, hcoef, houter]
  symm
  calc
    _ = ((m : ℝ) ^ (-(1 : ℝ) / 2) *
        Real.exp (Real.log (m : ℝ) / 2)) *
        (Real.exp (u / 2) *
          (4 * (Real.pi * (m : ℝ) ^ 2) ^ 2 * Real.exp (4 * u) -
            6 * (Real.pi * (m : ℝ) ^ 2) * Real.exp (2 * u)) *
          Real.exp (-(Real.pi * (m : ℝ) ^ 2) * Real.exp (2 * u))) := by ring
    _ = 1 *
        (Real.exp (u / 2) *
          (4 * (Real.pi * (m : ℝ) ^ 2) ^ 2 * Real.exp (4 * u) -
            6 * (Real.pi * (m : ℝ) ^ 2) * Real.exp (2 * u)) *
          Real.exp (-(Real.pi * (m : ℝ) ^ 2) * Real.exp (2 * u))) := by
      rw [hhalf_factor]
    _ = _ := by ring

/-- The aggregate translated-shell equality. The `Summable` premise records the
source's convergence qualification; the equality follows termwise, so Lean's
`tsum` need not choose a separate convergence convention. -/
theorem aggregateThetaKernelTranslatedShellSum_4662 (u : ℝ) :
    let Φ : ℕ → ℝ := fun m =>
      if 1 ≤ m then
        Real.exp (u / 2) *
            (4 * (Real.pi * (m : ℝ) ^ 2) ^ 2 * Real.exp (4 * u) -
              6 * (Real.pi * (m : ℝ) ^ 2) * Real.exp (2 * u)) *
            Real.exp (-(Real.pi * (m : ℝ) ^ 2) * Real.exp (2 * u))
      else 0
    let Ψ : ℕ → ℝ := fun m =>
      if 1 ≤ m then
        (m : ℝ) ^ (-(1 : ℝ) / 2) *
          (Real.exp ((u + Real.log (m : ℝ)) / 2) *
            (4 * Real.pi ^ 2 * Real.exp (4 * (u + Real.log (m : ℝ))) -
              6 * Real.pi * Real.exp (2 * (u + Real.log (m : ℝ)))) *
            Real.exp (-Real.pi * Real.exp (2 * (u + Real.log (m : ℝ)))))
      else 0
    Summable Φ → (∑' m : ℕ, Φ m) = ∑' m : ℕ, Ψ m := by
  dsimp
  intro _
  apply tsum_congr
  intro m
  by_cases hm : 1 ≤ m
  · simp only [if_pos hm]
    exact thetaShellTranslationPointwise_4662 m hm u
  · simp [hm]

end MathlibPlus.Analysis.ThetaShell
