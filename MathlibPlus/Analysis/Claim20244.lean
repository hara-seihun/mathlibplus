import MathlibPlus.Basic

namespace MathlibPlus.Analysis.Claim20244

/-- The paper's natural Riemann--Siegel cutoff, with the parameter `t` left
explicit rather than hiding the three source parameter values. -/
noncomputable def paperCutoff (x t : ℝ) : ℕ :=
  ⌊Real.sqrt (x / (4 * Real.pi) + t / 16)⌋₊

theorem paperCutoff_formula (x t : ℝ) :
    paperCutoff x t =
      ⌊Real.sqrt (x / (4 * Real.pi) + t / 16)⌋₊ := rfl

/-- The exact floor certificate for the numerical value in claim 20244.
The source record names three tested parameter sets but does not retain their
values, so their missing numerical hypotheses are exposed rather than
silently invented. -/
theorem paperCutoff_690988_of_bounds (t : ℝ)
    (hlo : (690988 : ℝ) ^ 2 ≤
      (6000000185827 : ℝ) / (4 * Real.pi) + t / 16)
    (hhi :
      (6000000185827 : ℝ) / (4 * Real.pi) + t / 16 <
        ((690988 : ℝ) + 1) ^ 2) :
    paperCutoff 6000000185827 t = 690988 := by
  let z : ℝ :=
    (6000000185827 : ℝ) / (4 * Real.pi) + t / 16
  change (690988 : ℝ) ^ 2 ≤ z at hlo
  change z < ((690988 : ℝ) + 1) ^ 2 at hhi
  have hz0 : 0 ≤ z := by
    nlinarith [hlo]
  have hsqrt_lower : (690988 : ℝ) ≤ Real.sqrt z := by
    have hs := Real.sq_sqrt hz0
    have hsn := Real.sqrt_nonneg z
    nlinarith [hlo]
  have hsqrt_upper : Real.sqrt z < (690988 : ℝ) + 1 := by
    have hs := Real.sq_sqrt hz0
    have hsn := Real.sqrt_nonneg z
    nlinarith [hhi]
  change ⌊Real.sqrt z⌋₊ = 690988
  exact (Nat.floor_eq_iff (Real.sqrt_nonneg z)).2 ⟨hsqrt_lower, hsqrt_upper⟩

end MathlibPlus.Analysis.Claim20244
