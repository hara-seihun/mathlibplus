import Mathlib

namespace MathlibPlus.Analysis.Claim46310

/-- Corrected evaluation of the displayed logarithmic tail integral. -/
theorem corrected_tail_integral (c lam δ : ℝ)
    (hc : 0 < c) (hlam : 0 < lam) (hδ : lam < δ) :
    3 * (∫ u in lam..δ, (-c * Real.log u) / u ^ 4) =
      c * (Real.log δ / δ ^ 3 - Real.log lam / lam ^ 3) -
        (c / 3) * (lam⁻¹ ^ 3 - δ⁻¹ ^ 3) := by
  let F : ℝ → ℝ := fun u =>
    c * (Real.log u + 1 / 3) * (u ^ 3)⁻¹
  have hpos : ∀ x ∈ Set.uIcc lam δ, 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le hδ.le] at hx
    exact lt_of_lt_of_le hlam hx.1
  have hF : ∀ x ∈ Set.uIcc lam δ,
      HasDerivAt F (3 * (-c * Real.log x) / x ^ 4) x := by
    intro x hx
    have hxpos : 0 < x := hpos x hx
    have hxne : x ≠ 0 := ne_of_gt hxpos
    have hlog : HasDerivAt (fun y : ℝ => Real.log y + 1 / 3) x⁻¹ x :=
      (Real.hasDerivAt_log hxne).add_const (1 / 3)
    have hpow : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
      simpa using hasDerivAt_pow 3 x
    have hinv : HasDerivAt (fun y : ℝ => (y ^ 3)⁻¹)
        (-(3 * x ^ 2) / (x ^ 3) ^ 2) x :=
      hpow.inv (pow_ne_zero 3 hxne)
    have hprod := (hlog.mul hinv).const_mul c
    have hfun : F =
        (fun y : ℝ => c * ((Real.log y + 1 / 3) * (y ^ 3)⁻¹)) := by
      funext y
      dsimp [F]
      ring
    rw [hfun]
    have hder : 3 * (-c * Real.log x) / x ^ 4 =
        c * (x⁻¹ * (x ^ 3)⁻¹ + (Real.log x + 1 / 3) *
          (-(3 * x ^ 2) / (x ^ 3) ^ 2)) := by
      field_simp [hxne]
      ring
    rw [hder]
    exact hprod
  have hcont : ContinuousOn
      (fun x : ℝ => 3 * (-c * Real.log x) / x ^ 4) (Set.uIcc lam δ) := by
    have hlogcont : ContinuousOn Real.log (Set.uIcc lam δ) :=
      Real.continuousOn_log.mono (by
        intro x hx
        exact Set.mem_compl_singleton_iff.mpr (ne_of_gt (hpos x hx)))
    have hnum : ContinuousOn
        (fun x : ℝ => 3 * (-c * Real.log x)) (Set.uIcc lam δ) := by
      simpa [mul_assoc] using (hlogcont.const_mul (-c)).const_mul 3
    have hden : ContinuousOn (fun x : ℝ => x ^ 4) (Set.uIcc lam δ) :=
      continuousOn_id' _ |>.pow 4
    exact hnum.div hden (by
      intro x hx
      exact pow_ne_zero 4 (ne_of_gt (hpos x hx)))
  have hEqDeriv : Set.EqOn
      (fun x : ℝ => 3 * (-c * Real.log x) / x ^ 4) (deriv F)
      (Set.uIoc lam δ) := by
    intro x hx
    exact (hF x (Set.uIoc_subset_uIcc hx)).deriv.symm
  have hfund :
      ∫ u in lam..δ, deriv F u = F δ - F lam := by
    apply intervalIntegral.integral_deriv_eq_sub
    · intro x hx
      exact (hF x hx).differentiableAt
    · exact hcont.intervalIntegrable.congr hEqDeriv
  have hEq :
      (∫ u in lam..δ, 3 * (-c * Real.log u) / u ^ 4) = F δ - F lam := by
    calc
      (∫ u in lam..δ, 3 * (-c * Real.log u) / u ^ 4) =
          ∫ u in lam..δ, deriv F u := by
            apply intervalIntegral.integral_congr
            intro x hx
            exact (hF x hx).deriv.symm
      _ = F δ - F lam := hfund
  calc
    3 * (∫ u in lam..δ, (-c * Real.log u) / u ^ 4) =
        ∫ u in lam..δ, 3 * ((-c * Real.log u) / u ^ 4) := by
          rw [intervalIntegral.integral_const_mul]
    _ = ∫ u in lam..δ, 3 * (-c * Real.log u) / u ^ 4 := by
      apply intervalIntegral.integral_congr
      intro u hu
      ring
    _ = F δ - F lam := hEq
    _ = c * (Real.log δ / δ ^ 3 - Real.log lam / lam ^ 3) -
          (c / 3) * (lam⁻¹ ^ 3 - δ⁻¹ ^ 3) := by
      dsimp [F]
      field_simp [ne_of_gt hlam, ne_of_gt (lt_trans hlam hδ)]
      ring

end MathlibPlus.Analysis.Claim46310
