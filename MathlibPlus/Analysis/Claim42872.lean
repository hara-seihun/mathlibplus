import Mathlib

namespace MathlibPlus.Analysis.Claim42872

/-- At a positive odd center, the cosine zero kills the derivative of the
Gamma factor in the reflected Gamma reference. -/
theorem reflectedGammaDerivative_claim42872 (n : ℕ) :
    let R : ℝ → ℝ := fun x =>
      Real.Gamma ((x + 1) / 2) * Real.cos (Real.pi * x / 2) / Real.pi
    deriv R (2 * (n : ℝ) + 1) =
      Real.Gamma (n + 1) *
        (-Real.sin (Real.pi * (2 * (n : ℝ) + 1) / 2) * Real.pi / 2) /
          Real.pi := by
  dsimp
  let x₀ : ℝ := 2 * (n : ℝ) + 1
  have hx₀ : x₀ = 2 * (n : ℝ) + 1 := rfl
  have harg : HasDerivAt (fun x : ℝ => (x + 1) / 2) (1 / 2) x₀ := by
    simpa [id_eq] using ((hasDerivAt_id x₀).add_const 1).div_const 2
  have hargcos : HasDerivAt (fun x : ℝ => Real.pi * x / 2)
      (Real.pi / 2) x₀ := by
    simpa [id_eq] using ((hasDerivAt_id x₀).const_mul Real.pi).div_const 2
  have hpos : 0 < (x₀ + 1) / 2 := by
    dsimp [x₀]
    positivity
  have hG : HasDerivAt (fun x : ℝ => Real.Gamma ((x + 1) / 2))
      (deriv Real.Gamma ((x₀ + 1) / 2) * (1 / 2)) x₀ := by
    exact (Real.differentiableAt_Gamma (fun m => by
      intro hm
      have hm_nonpos : -(m : ℝ) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg m)
      linarith [hpos]
    )).hasDerivAt.comp x₀ harg
  have hcos : HasDerivAt (fun x : ℝ => Real.cos (Real.pi * x / 2))
      (-Real.sin (Real.pi * x₀ / 2) * (Real.pi / 2)) x₀ := by
    exact (Real.hasDerivAt_cos _).comp x₀ hargcos
  have hprod := (hG.mul hcos).div_const Real.pi
  have hd : deriv (fun x : ℝ => Real.Gamma ((x + 1) / 2) *
      Real.cos (Real.pi * x / 2) / Real.pi) x₀ =
      ((deriv Real.Gamma ((x₀ + 1) / 2) * (1 / 2)) *
        Real.cos (Real.pi * x₀ / 2) +
        Real.Gamma ((x₀ + 1) / 2) *
          (-Real.sin (Real.pi * x₀ / 2) * (Real.pi / 2))) / Real.pi :=
    hprod.deriv
  rw [show (2 * (n : ℝ) + 1) = x₀ by rfl]
  rw [hd]
  have hcoszero : Real.cos (Real.pi * x₀ / 2) = 0 := by
    dsimp [x₀]
    rw [show Real.pi * (2 * (n : ℝ) + 1) / 2 =
        (n : ℝ) * Real.pi + Real.pi / 2 by ring]
    rw [Real.cos_add]
    simp
  rw [hcoszero]
  congr 2
  dsimp [x₀]
  ring

end MathlibPlus.Analysis.Claim42872
