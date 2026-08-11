import Mathlib

namespace MathlibPlus.Analysis

open Set

/-- A strict endpoint sign change, together with exclusion of derivative zeros on the
closed interval, isolates one interior zero and certifies its simplicity. -/
theorem uniqueSimpleZero_of_signChange_of_deriv_ne_zero
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : Differentiable ℝ f)
    (hsign : f a * f b < 0)
    (hderiv : ∀ x ∈ Icc a b, deriv f x ≠ 0) :
    ∃! x : ℝ, x ∈ Ioo a b ∧ f x = 0 ∧ deriv f x ≠ 0 := by
  have hcont : ContinuousOn f (Icc a b) := hf.continuous.continuousOn
  have hz : (0 : ℝ) ∈ Icc (f a) (f b) ∨ (0 : ℝ) ∈ Icc (f b) (f a) := by
    rcases (mul_neg_iff.mp hsign) with h | h
    · exact Or.inr ⟨h.2.le, h.1.le⟩
    · exact Or.inl ⟨h.1.le, h.2.le⟩
  obtain ⟨x, hxIcc, hfx⟩ : ∃ x ∈ Icc a b, f x = 0 := by
    rcases hz with hz | hz
    · rcases intermediate_value_Icc hab.le hcont hz with ⟨x, hx, hxeq⟩
      exact ⟨x, hx, hxeq⟩
    · rcases intermediate_value_Icc' hab.le hcont hz with ⟨x, hx, hxeq⟩
      exact ⟨x, hx, hxeq⟩
  have hfa : f a ≠ 0 := by
    intro ha
    simp [ha] at hsign
  have hfb : f b ≠ 0 := by
    intro hb
    simp [hb] at hsign
  have hxIoo : x ∈ Ioo a b := by
    refine ⟨lt_of_le_of_ne hxIcc.1 ?_, lt_of_le_of_ne hxIcc.2 ?_⟩
    · intro hxa
      apply hfa
      rw [hxa]
      exact hfx
    · intro hxb
      apply hfb
      rw [← hxb]
      exact hfx
  refine ⟨x, ⟨hxIoo, hfx, hderiv x ⟨hxIoo.1.le, hxIoo.2.le⟩⟩, ?_⟩
  intro y hy
  by_contra hxy
  rcases lt_or_gt_of_ne hxy with hyx | hxy
  · obtain ⟨c, hc, hcderiv⟩ := exists_deriv_eq_slope f hyx
        hf.continuous.continuousOn hf.differentiableOn
    have hcIcc : c ∈ Icc a b := by
      constructor <;> linarith [hy.1.1, hy.1.2, hxIoo.1, hxIoo.2, hc.1, hc.2]
    apply hderiv c hcIcc
    rw [hcderiv, hfx, hy.2.1, sub_self, zero_div]
  · obtain ⟨c, hc, hcderiv⟩ := exists_deriv_eq_slope f hxy
        hf.continuous.continuousOn hf.differentiableOn
    have hcIcc : c ∈ Icc a b := by
      constructor <;> linarith [hy.1.1, hy.1.2, hxIoo.1, hxIoo.2, hc.1, hc.2]
    apply hderiv c hcIcc
    rw [hcderiv, hy.2.1, hfx, sub_self, zero_div]

noncomputable section HardyTransform

/-- Real differentiation of a complex-valued function, using the real-complex
normed-algebra module structure selected by multiplication's derivative rule. -/
abbrev HasRealDerivAt (f : ℝ → ℂ) (f' : ℂ) (x : ℝ) : Prop :=
  @HasDerivAt ℝ _ ℂ
    instCommCStarAlgebraComplex.toCStarAlgebra.toAddCommGroup
    (NormedAlgebra.toNormedSpace ℂ).toModule _ _ f f' x

/-- At a zero, differentiating a Hardy transform kills the phase-derivative term.
This is the exact mechanism behind `Z'(t) = i exp(i θ(t)) ζ'(1/2+it)`. -/
theorem hardyTransform_hasDerivAt_at_zero
    {ζ : ℂ → ℂ} {ζ' : ℂ} {θ : ℝ → ℝ} {θ' t : ℝ}
    (hζ : HasDerivAt ζ ζ' ((1 / 2 : ℂ) + Complex.I * t))
    (hθ : HasDerivAt θ θ' t)
    (hzero : ζ ((1 / 2 : ℂ) + Complex.I * t) = 0) :
    HasRealDerivAt
      (fun s : ℝ => Complex.exp (Complex.I * θ s) *
        ζ ((1 / 2 : ℂ) + Complex.I * s))
      (Complex.I * Complex.exp (Complex.I * θ t) * ζ') t := by
  have hline : HasRealDerivAt
      (fun s : ℝ => (1 / 2 : ℂ) + Complex.I * s) Complex.I t := by
    simpa using ((hasDerivAt_id t).ofReal_comp.const_mul Complex.I).const_add (1 / 2 : ℂ)
  have hζline : HasRealDerivAt
      (fun s : ℝ => ζ ((1 / 2 : ℂ) + Complex.I * s)) (ζ' * Complex.I) t := by
    simpa [Function.comp_def] using hζ.complexToReal_fderiv.comp_hasDerivAt t hline
  have hphase : HasRealDerivAt
      (fun s : ℝ => Complex.exp (Complex.I * θ s))
      (Complex.exp (Complex.I * θ t) * (Complex.I * θ')) t := by
    simpa using (hθ.ofReal_comp.const_mul Complex.I).cexp
  have hprod : HasRealDerivAt
      (fun s : ℝ => Complex.exp (Complex.I * θ s) *
        ζ ((1 / 2 : ℂ) + Complex.I * s))
      (Complex.exp (Complex.I * θ t) * (Complex.I * θ') *
          ζ ((1 / 2 : ℂ) + Complex.I * t) +
        Complex.exp (Complex.I * θ t) * (ζ' * Complex.I)) t := by
    exact hphase.mul hζline
  convert hprod using 1
  · rw [hzero]
    ring

/-- Nonvanishing of a Hardy-transform derivative at a zero forces nonvanishing of
the corresponding complex derivative. -/
theorem complexDeriv_ne_zero_of_hardyTransform_deriv_ne_zero
    {ζ' θt Z' : ℂ}
    (hZ' : Z' = Complex.I * Complex.exp (Complex.I * θt) * ζ')
    (hne : Z' ≠ 0) : ζ' ≠ 0 := by
  intro hζ'
  apply hne
  simp [hZ', hζ']

end HardyTransform

end MathlibPlus.Analysis
