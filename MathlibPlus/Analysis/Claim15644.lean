import Mathlib

namespace MathlibPlus.Analysis.Claim15644

/-- A finite positive family of slopes, none equal to the positive reference slope,
has a uniform positive lower bound for the logarithmic gaps. -/
theorem uniformPositiveSlopeGap
    (S : Finset ℝ) (d : ℝ) (hS : S.Nonempty) (hd : 0 < d)
    (hpos : ∀ s ∈ S, 0 < s) (hne : d ∉ S) :
    ∃ ε > 0, ∀ s ∈ S, ε ≤ s - d - d * Real.log (s / d) := by
  have hgap : ∀ s ∈ S, 0 < s - d - d * Real.log (s / d) := by
    intro s hs
    have hspos : 0 < s := hpos s hs
    have hratio : 0 < s / d := div_pos hspos hd
    have hratio_ne : s / d ≠ 1 := by
      intro h
      apply hne
      have hs_eq : s = d := (div_eq_one_iff_eq hd.ne').mp h
      exact hs_eq ▸ hs
    have hlog : Real.log (s / d) < s / d - 1 :=
      Real.log_lt_sub_one_of_pos hratio hratio_ne
    have hscaled : 0 < d * (s / d - 1 - Real.log (s / d)) :=
      mul_pos hd (sub_pos.mpr hlog)
    convert hscaled using 1 <;> field_simp [hd.ne']
  obtain ⟨s₀, hs₀, hmin⟩ := S.exists_min_image
    (fun s => s - d - d * Real.log (s / d)) hS
  refine ⟨(s₀ - d - d * Real.log (s₀ / d)) / 2, ?_, ?_⟩
  · linarith [hgap s₀ hs₀]
  · intro s hs
    have hle := hmin s hs
    linarith [hgap s₀ hs₀]

end MathlibPlus.Analysis.Claim15644
