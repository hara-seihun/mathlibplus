import Mathlib

namespace MathlibPlus.ComplexGeometry.Claim32786

private lemma side_sub_norm
    {V : Type*} [SeminormedAddCommGroup V] (u v : V) (hv : ‖v‖ = 1) :
    ‖u - (u + v)‖ = 1 := by
  simpa [sub_eq_add_neg, add_assoc, norm_neg] using hv

private lemma side_add_norm
    {V : Type*} [SeminormedAddCommGroup V] (u v : V) (hu : ‖u‖ = 1) :
    ‖v - (u + v)‖ = 1 := by
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, norm_neg] using hu

/-- Claim 32786: the rhombus has four unit sides and the two displayed
squared diagonal lengths.  The strict inequalities show that, for
`0 < a < 1/2`, the diagonals are not unit edges. -/
theorem fourPointRhombusDistances
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (a : ℝ) (u v : V)
    (ha₀ : 0 < a) (ha_half : a < 1 / 2)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner ℝ u v = a) :
    dist (0 : V) u = 1 ∧
      dist (0 : V) v = 1 ∧
      dist u (u + v) = 1 ∧
      dist v (u + v) = 1 ∧
      1 < dist u v ∧
      1 < dist (0 : V) (u + v) ∧
      dist u v ^ 2 = 2 - 2 * a ∧
      dist (0 : V) (u + v) ^ 2 = 2 + 2 * a := by
  have hsubsq : ‖u - v‖ ^ 2 = 2 - 2 * a := by
    rw [norm_sub_sq_real, hu, hv, huv]
    ring
  have haddsq : ‖u + v‖ ^ 2 = 2 + 2 * a := by
    rw [norm_add_sq_real, hu, hv, huv]
    ring
  have hsub_gt : 1 < ‖u - v‖ := by
    nlinarith [norm_nonneg (u - v), ha_half]
  have hadd_gt : 1 < ‖u + v‖ := by
    nlinarith [norm_nonneg (u + v), ha₀]
  have hzero_sub_norm : ‖(0 : V) - (u + v)‖ = ‖u + v‖ := by
    rw [zero_sub, norm_neg]
  have hadd_gt_zero : 1 < ‖(0 : V) - (u + v)‖ := by
    rw [hzero_sub_norm]
    exact hadd_gt
  have hzero_u : dist (0 : V) u = 1 := by
    simpa [dist_eq_norm] using hu
  have hzero_v : dist (0 : V) v = 1 := by
    simpa [dist_eq_norm] using hv
  have hu_sum : dist u (u + v) = 1 := by
    rw [dist_eq_norm]
    exact side_sub_norm u v hv
  have hv_sum : dist v (u + v) = 1 := by
    rw [dist_eq_norm]
    exact side_add_norm u v hu
  have huv_dist : dist u v ^ 2 = 2 - 2 * a := by
    simpa [dist_eq_norm] using hsubsq
  have hzero_sum_dist : dist (0 : V) (u + v) ^ 2 = 2 + 2 * a := by
    rw [dist_eq_norm, zero_sub, norm_neg]
    exact haddsq
  exact ⟨hzero_u, hzero_v, hu_sum, hv_sum,
    by simpa [dist_eq_norm] using hsub_gt,
    by simpa [dist_eq_norm] using hadd_gt_zero,
    huv_dist, hzero_sum_dist⟩

/-- At the endpoint `a = 1/2`, the shorter diagonal is also a unit edge;
the two triangles on the common side `u--v` are equilateral. -/
theorem fourPointRhombusAtHalf
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner ℝ u v = 1 / 2) :
    dist (0 : V) u = 1 ∧
      dist (0 : V) v = 1 ∧
      dist u v = 1 ∧
      dist u (u + v) = 1 ∧
      dist v (u + v) = 1 ∧
      dist (0 : V) (u + v) = Real.sqrt 3 ∧
      (dist (0 : V) u = 1 ∧ dist (0 : V) v = 1 ∧ dist u v = 1) ∧
      (dist u v = 1 ∧ dist u (u + v) = 1 ∧ dist v (u + v) = 1) := by
  have hsubsq : ‖u - v‖ ^ 2 = 1 := by
    rw [norm_sub_sq_real, hu, hv, huv]
    norm_num
  have haddsq : ‖u + v‖ ^ 2 = 3 := by
    rw [norm_add_sq_real, hu, hv, huv]
    norm_num
  have hsub : ‖u - v‖ = 1 := by
    nlinarith [norm_nonneg (u - v)]
  have hadd : ‖u + v‖ = Real.sqrt 3 := by
    have hsqrt : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by norm_num
    nlinarith [norm_nonneg (u + v), Real.sqrt_nonneg (3 : ℝ)]
  have hzero_u : dist (0 : V) u = 1 := by
    simpa [dist_eq_norm] using hu
  have hzero_v : dist (0 : V) v = 1 := by
    simpa [dist_eq_norm] using hv
  have huv_dist : dist u v = 1 := by
    simpa [dist_eq_norm] using hsub
  have hu_sum : dist u (u + v) = 1 := by
    rw [dist_eq_norm]
    exact side_sub_norm u v hv
  have hv_sum : dist v (u + v) = 1 := by
    rw [dist_eq_norm]
    exact side_add_norm u v hu
  have hzero_sum : dist (0 : V) (u + v) = Real.sqrt 3 := by
    rw [dist_eq_norm, zero_sub, norm_neg]
    exact hadd
  exact ⟨hzero_u, hzero_v, huv_dist, hu_sum, hv_sum, hzero_sum,
    ⟨hzero_u, hzero_v, huv_dist⟩,
    ⟨huv_dist, hu_sum, hv_sum⟩⟩

end MathlibPlus.ComplexGeometry.Claim32786
