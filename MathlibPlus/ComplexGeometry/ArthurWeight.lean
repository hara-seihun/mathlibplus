import MathlibPlus.ComplexGeometry.ReflectedWedge

namespace MathlibPlus.ComplexGeometry

/-- Hyperbolic representative `h_U=(e^(U/2),e^(-U/2))`. -/
noncomputable def arthurHyperbolicWeight (U : ℝ) : ℂ × ℂ :=
  (Real.exp (U / 2), Real.exp (-U / 2))

/-- Circular representative `c_Φ=(e^(iΦ/2),e^(-iΦ/2))`. -/
noncomputable def arthurCircularWeight (Φ : ℝ) : ℂ × ℂ :=
  (⟨Real.cos (Φ / 2), Real.sin (Φ / 2)⟩,
    ⟨Real.cos (Φ / 2), -Real.sin (Φ / 2)⟩)

/-- Direct Arthur-weight energy `|ω(h_U,c_Φ)|²`. -/
noncomputable def arthurDirectEnergy (U Φ : ℝ) : ℝ :=
  Complex.normSq (wedge (arthurHyperbolicWeight U) (arthurCircularWeight Φ))

/-- Reflected Arthur-weight energy `|ω(h_U,Jc_Φ)|²`. -/
noncomputable def arthurReflectedEnergy (U Φ : ℝ) : ℝ :=
  Complex.normSq (wedge (arthurHyperbolicWeight U)
    (reflectedJ (arthurCircularWeight Φ)))

private theorem exp_half_sq (U : ℝ) : Real.exp (U / 2) ^ 2 = Real.exp U := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

private theorem exp_neg_half_sq (U : ℝ) : Real.exp (-U / 2) ^ 2 = Real.exp (-U) := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

private theorem exp_half_mul_exp_neg_half (U : ℝ) :
    Real.exp (U / 2) * Real.exp (-U / 2) = 1 := by
  rw [← Real.exp_add]
  convert Real.exp_zero
  ring

/-- The direct and reflected energies of one Arthur weight, together with their
reflected-cone margin. -/
theorem arthurWeightEnergies (U Φ : ℝ) :
    arthurDirectEnergy U Φ = Real.exp U + Real.exp (-U) - 2 * Real.cos Φ ∧
      arthurReflectedEnergy U Φ = Real.exp U + Real.exp (-U) + 2 * Real.cos Φ ∧
      2 * arthurReflectedEnergy U Φ - arthurDirectEnergy U Φ =
        Real.exp U + Real.exp (-U) + 6 * Real.cos Φ := by
  have htrig :
      Real.cos (Φ / 2) ^ 2 - Real.sin (Φ / 2) ^ 2 = Real.cos Φ := by
    calc
      Real.cos (Φ / 2) ^ 2 - Real.sin (Φ / 2) ^ 2 =
          Real.cos (2 * (Φ / 2)) := (Real.cos_two_mul' (Φ / 2)).symm
      _ = Real.cos Φ := by congr 1 <;> ring
  have htrigSum :
      Real.cos (Φ / 2) ^ 2 + Real.sin (Φ / 2) ^ 2 = 1 := by
    exact Real.cos_sq_add_sin_sq (Φ / 2)
  have hWedgeD :
      wedge (arthurHyperbolicWeight U) (arthurCircularWeight Φ) =
        (((Real.exp (U / 2) - Real.exp (-U / 2)) * Real.cos (Φ / 2) : ℝ) : ℂ) -
          (((Real.exp (U / 2) + Real.exp (-U / 2)) * Real.sin (Φ / 2) : ℝ) : ℂ) *
            Complex.I := by
    unfold wedge arthurHyperbolicWeight arthurCircularWeight
    apply Complex.ext <;>
      simp only [Prod.fst, Prod.snd, Complex.sub_re, Complex.sub_im, Complex.add_re,
        Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im] <;>
      norm_num <;> ring
  have hReflect :
      reflectedJ (arthurCircularWeight Φ) =
        (⟨Real.cos (Φ / 2), -Real.sin (Φ / 2)⟩,
          -⟨Real.cos (Φ / 2), Real.sin (Φ / 2)⟩) := by
    apply Prod.ext <;> apply Complex.ext <;>
      simp [reflectedJ, arthurCircularWeight]
  have hWedgeR :
      wedge (arthurHyperbolicWeight U) (reflectedJ (arthurCircularWeight Φ)) =
        ((-(Real.exp (U / 2) + Real.exp (-U / 2)) * Real.cos (Φ / 2) : ℝ) : ℂ) +
          (((Real.exp (-U / 2) - Real.exp (U / 2)) * Real.sin (Φ / 2) : ℝ) : ℂ) *
            Complex.I := by
    rw [hReflect]
    unfold wedge arthurHyperbolicWeight
    apply Complex.ext <;>
      simp only [Prod.fst, Prod.snd, Complex.sub_re, Complex.sub_im, Complex.add_re,
        Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im] <;>
      norm_num <;> ring
  have hD :
      arthurDirectEnergy U Φ = Real.exp U + Real.exp (-U) - 2 * Real.cos Φ := by
    rw [arthurDirectEnergy, hWedgeD]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    norm_num
    nlinarith [exp_half_sq U, exp_neg_half_sq U, exp_half_mul_exp_neg_half U]
  have hR :
      arthurReflectedEnergy U Φ = Real.exp U + Real.exp (-U) + 2 * Real.cos Φ := by
    rw [arthurReflectedEnergy, hWedgeR]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    norm_num
    nlinarith [exp_half_sq U, exp_neg_half_sq U, exp_half_mul_exp_neg_half U]
  refine ⟨hD, hR, ?_⟩
  rw [hD, hR]
  ring

end MathlibPlus.ComplexGeometry
