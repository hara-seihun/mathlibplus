import Mathlib

open scoped Interval

namespace MathlibPlus.Analysis.Claim2024

/-- The normalized increasing affine weight from admitted claim 2024.
The local `J` is the source's endpoint-plus-weighted-variation functional. -/
theorem normalizedIncreasingAffineWeight_claim2024 (ξ : ℝ) (hξ : 1 < ξ) :
    let w : ℝ → ℝ := fun u => 2 * (u - 1) / (ξ - 1) ^ 2
    let J : (ℝ → ℝ) → ℝ := fun f =>
      f ξ / ξ + f 1 +
        (∫ u in (1 : ℝ)..ξ, f u / u) +
        (∫ u in (1 : ℝ)..ξ, |deriv f u| / u)
    (∫ u in (1 : ℝ)..ξ, w u) = 1 ∧
      (∀ t : ℝ, 0 < t → t < 2 / (ξ - 1) →
        {u : ℝ | u ∈ Set.Icc (1 : ℝ) ξ ∧ t < w u} =
          Set.Ioc (1 + t * (ξ - 1) ^ 2 / 2) ξ) ∧
      J w = 2 / (ξ - 1) * (1 + 1 / ξ) := by
  dsimp
  have hξ1 : 0 < ξ - 1 := sub_pos.mpr hξ
  have hξ1ne : ξ - 1 ≠ 0 := ne_of_gt hξ1
  have hξne : ξ ≠ 0 := by linarith
  have hzero : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) ξ := by
    rw [Set.uIcc_of_le hξ.le]
    simp only [Set.mem_Icc, not_and]
    intro h
    linarith
  have hderiv : ∀ u : ℝ,
      deriv (fun x : ℝ => 2 * (x - 1) / (ξ - 1) ^ 2) u =
        2 / (ξ - 1) ^ 2 := by
    intro u
    have h := ((hasDerivAt_id u).sub_const (1 : ℝ)).const_mul 2
    have h' := h.div_const ((ξ - 1) ^ 2)
    simpa using h'.deriv
  have hnorm :
      (∫ u in (1 : ℝ)..ξ, 2 * (u - 1) / (ξ - 1) ^ 2) = 1 := by
    have hid : IntervalIntegrable (fun u : ℝ => u) MeasureTheory.volume 1 ξ :=
      (continuousOn_id' (Set.uIcc (1 : ℝ) ξ)).intervalIntegrable
    have hconst : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) MeasureTheory.volume 1 ξ :=
      intervalIntegrable_const
    have hfun : (fun u : ℝ => 2 * (u - 1) / (ξ - 1) ^ 2) =
        (fun u => (2 / (ξ - 1) ^ 2) * (u - 1)) := by
      funext u
      field_simp [hξ1ne]
    have hsub :
        (∫ u in (1 : ℝ)..ξ, u - 1) =
          (∫ u in (1 : ℝ)..ξ, u) - (∫ u in (1 : ℝ)..ξ, (1 : ℝ)) :=
      intervalIntegral.integral_sub hid hconst
    calc
      (∫ u in (1 : ℝ)..ξ, 2 * (u - 1) / (ξ - 1) ^ 2) =
          (2 / (ξ - 1) ^ 2) * (∫ u in (1 : ℝ)..ξ, u - 1) := by
            rw [hfun, intervalIntegral.integral_const_mul]
      _ = 1 := by
        rw [hsub, integral_id, intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        field_simp [hξ1ne] <;> ring
  have hsuper :
      ∀ t : ℝ, 0 < t → t < 2 / (ξ - 1) →
        {u : ℝ | u ∈ Set.Icc (1 : ℝ) ξ ∧
          t < 2 * (u - 1) / (ξ - 1) ^ 2} =
          Set.Ioc (1 + t * (ξ - 1) ^ 2 / 2) ξ := by
    intro t ht0 htmax
    ext u
    constructor
    · intro hu
      rcases hu with ⟨huIcc, hut⟩
      have huupper : u ≤ ξ := huIcc.2
      have hdenpos : 0 < (ξ - 1) ^ 2 := sq_pos_of_pos hξ1
      have hlow : 1 + t * (ξ - 1) ^ 2 / 2 < u := by
        have hmul : t * (ξ - 1) ^ 2 < 2 * (u - 1) := by
          have h := hut
          field_simp [hdenpos.ne'] at h
          nlinarith
        nlinarith
      exact ⟨hlow, huupper⟩
    · intro hu
      rcases hu with ⟨hulow, huupper⟩
      have hdenpos : 0 < (ξ - 1) ^ 2 := sq_pos_of_pos hξ1
      constructor
      · constructor
        · have htpos : 0 < t * (ξ - 1) ^ 2 / 2 := by positivity
          linarith
        · exact huupper
      · have hmul : t * (ξ - 1) ^ 2 < 2 * (u - 1) := by
          nlinarith
        field_simp [hdenpos.ne']
        nlinarith
  have hJ :
      (2 * (ξ - 1) / (ξ - 1) ^ 2) / ξ +
          2 * (1 - 1) / (ξ - 1) ^ 2 +
        (∫ u in (1 : ℝ)..ξ, (2 * (u - 1) / (ξ - 1) ^ 2) / u) +
        (∫ u in (1 : ℝ)..ξ,
          |deriv (fun x : ℝ => 2 * (x - 1) / (ξ - 1) ^ 2) u| / u) =
        2 / (ξ - 1) * (1 + 1 / ξ) := by
    simp_rw [hderiv]
    have hconstpos : 0 ≤ 2 / (ξ - 1) ^ 2 := by positivity
    have habs :
        (fun u : ℝ => |2 / (ξ - 1) ^ 2| / u) =
          (fun u : ℝ => (2 / (ξ - 1) ^ 2) / u) := by
      funext u
      rw [abs_of_nonneg hconstpos]
    rw [habs]
    have h_inv_cont :
        ContinuousOn (fun u : ℝ => 1 / u) (Set.uIcc (1 : ℝ) ξ) := by
      apply continuousOn_const.div (continuousOn_id' _)
      intro u hu
      exact ne_of_gt (by
        rw [Set.uIcc_of_le hξ.le] at hu
        linarith [hu.1])
    have h_inv : IntervalIntegrable (fun u : ℝ => 1 / u) MeasureTheory.volume 1 ξ :=
      h_inv_cont.intervalIntegrable
    have h_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) MeasureTheory.volume 1 ξ :=
      intervalIntegrable_const
    have hmain :
        (∫ u in (1 : ℝ)..ξ, (2 * (u - 1) / (ξ - 1) ^ 2) / u) =
          (2 / (ξ - 1) ^ 2) * (ξ - 1 - Real.log ξ) := by
      have hrewrite : ∀ u ∈ Set.uIcc (1 : ℝ) ξ,
          (2 * (u - 1) / (ξ - 1) ^ 2) / u =
            (2 / (ξ - 1) ^ 2) * (1 - 1 / u) := by
        intro u hu
        have hu0 : u ≠ 0 := by
          exact ne_of_gt (by
            rw [Set.uIcc_of_le hξ.le] at hu
            linarith [hu.1])
        field_simp [hξ1ne, hu0]
      have hrewrite_int :
          (∫ u in (1 : ℝ)..ξ, (2 * (u - 1) / (ξ - 1) ^ 2) / u) =
            ∫ u in (1 : ℝ)..ξ, (2 / (ξ - 1) ^ 2) * (1 - 1 / u) := by
        apply intervalIntegral.integral_congr
        intro u hu
        exact hrewrite u hu
      rw [hrewrite_int, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub h_const h_inv,
        intervalIntegral.integral_const, integral_one_div hzero]
      simp
    have hvar :
        (∫ u in (1 : ℝ)..ξ, (2 / (ξ - 1) ^ 2) / u) =
          (2 / (ξ - 1) ^ 2) * Real.log ξ := by
      rw [show (fun u : ℝ => (2 / (ξ - 1) ^ 2) / u) =
          (fun u => (2 / (ξ - 1) ^ 2) * (1 / u)) by
            funext u
            ring]
      rw [intervalIntegral.integral_const_mul, integral_one_div hzero]
      simp
    rw [hmain, hvar]
    field_simp [hξ1ne, hξne]
    ring
  exact ⟨hnorm, hsuper, hJ⟩

end MathlibPlus.Analysis.Claim2024
