import Mathlib

namespace MathlibPlus.Analysis.RegularVariation

/-- The explicit terminal-action integral from claim 8778.  The arbitrary
parameter `_A` records the source's `a(t) = A / t` context; the displayed
integral is independent of `A`. -/
theorem terminalActionIntegral (_A τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    (∫ t in τ..1, Real.log (2 * t / τ - 1)) =
      ((2 - τ) / 2) * Real.log ((2 - τ) / τ) - 1 + τ := by
  let f : ℝ → ℝ := fun t => 2 * (t / τ) - 1
  let F : ℝ → ℝ := fun t => (τ / 2) * (f t * Real.log (f t) - f t)
  have hτle : τ ≤ 1 := le_of_lt hτ1
  have hfcont : ContinuousOn f (Set.Icc τ 1) := by
    dsimp [f]
    have h : ContinuousOn
        ((fun x : ℝ => 2 * (id x / τ)) - (fun _ : ℝ => (1 : ℝ))) (Set.Icc τ 1) :=
      (((continuous_id.div_const τ).const_mul 2).sub
        (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ)))).continuousOn
    convert h using 1
    ext t
    simp [id]
  have hfpos : ∀ t ∈ Set.Icc τ 1, 0 < f t := by
    intro t ht
    dsimp [f]
    have hratio : 1 ≤ t / τ := by
      simpa using (le_div_iff₀ hτ0).2 (show 1 * τ ≤ t by simpa using ht.1)
    nlinarith
  have hlogcont : ContinuousOn (fun t => Real.log (f t)) (Set.Icc τ 1) := by
    exact hfcont.log (fun t ht => ne_of_gt (hfpos t ht))
  have hFcont : ContinuousOn F (Set.Icc τ 1) := by
    dsimp [F]
    exact (hfcont.mul hlogcont).sub hfcont |>.const_mul (τ / 2)
  have hderiv : ∀ x ∈ Set.Ioo τ 1, HasDerivAt F (Real.log (f x)) x := by
    intro x hx
    have hf : HasDerivAt f (2 * (1 / τ)) x := by
      dsimp [f]
      simpa only [id_eq] using
        (((hasDerivAt_id x).div_const τ).const_mul 2).sub_const 1
    have hfx : f x ≠ 0 := ne_of_gt (hfpos x ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
    have hlog : HasDerivAt (fun y => Real.log (f y)) ((2 * (1 / τ)) / f x) x :=
      hf.log hfx
    have hinner : HasDerivAt (fun y => f y * Real.log (f y) - f y)
        ((2 * (1 / τ)) * Real.log (f x) + f x * ((2 * (1 / τ)) / f x) - 2 * (1 / τ)) x := by
      exact (hf.mul hlog).sub hf
    have hF' := hinner.const_mul (τ / 2)
    have hval :
        (τ / 2) *
            (2 * (1 / τ) * Real.log (f x) +
              f x * ((2 * (1 / τ)) / f x) - 2 * (1 / τ)) =
          Real.log (f x) := by
      have hcancel : f x * ((2 * (1 / τ)) / f x) = 2 * (1 / τ) := by
        field_simp [hfx]
      rw [hcancel]
      field_simp [ne_of_gt hτ0]
      ring
    dsimp [F]
    rw [← hval]
    exact hF'
  have hint : IntervalIntegrable (fun t => Real.log (f t)) MeasureTheory.volume τ 1 :=
    hlogcont.intervalIntegrable_of_Icc hτle
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hτle hFcont hderiv hint
  have hrewrite : (fun t : ℝ => Real.log (f t)) = (fun t => Real.log (2 * t / τ - 1)) := by
    funext t
    simp only [f]
    congr 1
    ring
  rw [← hrewrite]
  calc
    (∫ (y : ℝ) in τ..1, Real.log (f y)) = F 1 - F τ := hfund
    _ = ((2 - τ) / 2) * Real.log ((2 - τ) / τ) - 1 + τ := by
      dsimp [F, f]
      have hτne : τ ≠ 0 := ne_of_gt hτ0
      have htau : 2 * (τ / τ) - 1 = 1 := by
        norm_num [hτne]
      have hone : 2 * (1 / τ) - 1 = (2 - τ) / τ := by field_simp
      rw [htau, hone, Real.log_one]
      field_simp [hτne]
      ring

end MathlibPlus.Analysis.RegularVariation
