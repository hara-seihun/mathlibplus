import Mathlib

namespace MathlibPlus.Geometry

/-- Endpoint pinning, isolated from the unspecified flex-space construction in claim 48840. -/
def EndpointPinned {ι V : Type*} [Zero V] (B : Finset ι) (w : ι → V) : Prop :=
  ∀ i, i ∈ B → w i = (0 : V)

/-- The exact quadratic contact expansion from claim 48840. -/
theorem claim48840_contact_expansion
    {ι V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {x w : ι → V} {i j : ι} {t : ℝ}
    (hbase : ‖x i - x j‖ ^ 2 = 1)
    (hflex : inner ℝ (x i - x j) (w i - w j) = 0) :
    ‖(x i + t • w i) - (x j + t • w j)‖ ^ 2 =
      1 + t ^ 2 * ‖w i - w j‖ ^ 2 := by
  have hbase' : inner ℝ (x i - x j) (x i - x j) = 1 := by
    rw [real_inner_self_eq_norm_sq]
    exact hbase
  calc
    ‖(x i + t • w i) - (x j + t • w j)‖ ^ 2 =
        inner ℝ ((x i + t • w i) - (x j + t • w j))
          ((x i + t • w i) - (x j + t • w j)) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = inner ℝ ((x i - x j) + t • (w i - w j))
          ((x i - x j) + t • (w i - w j)) := by
      rw [show (x i + t • w i) - (x j + t • w j) =
        (x i - x j) + t • (w i - w j) by module]
    _ = 1 + t ^ 2 * ‖w i - w j‖ ^ 2 := by
      simp only [inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, hflex, mul_zero, zero_mul, add_zero,
        real_inner_comm]
      rw [real_inner_self_eq_norm_sq (w i - w j)]
      nlinarith [hbase']

/-- A contact satisfying the expansion never gets shorter than its unit length. -/
theorem claim48840_contact_distance_ge_one
    {ι V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {x w : ι → V} {i j : ι} {t : ℝ}
    (hbase : ‖x i - x j‖ ^ 2 = 1)
    (hflex : inner ℝ (x i - x j) (w i - w j) = 0) :
    1 ≤ ‖(x i + t • w i) - (x j + t • w j)‖ := by
  have hexp := claim48840_contact_expansion (t := t) hbase hflex
  have hsquare : 1 ≤ ‖(x i + t • w i) - (x j + t • w j)‖ ^ 2 := by
    rw [hexp]
    nlinarith [sq_nonneg t, sq_nonneg ‖w i - w j‖]
  nlinarith [norm_nonneg ((x i + t • w i) - (x j + t • w j))]

/-- Strict opening occurs exactly when both the time and relative velocity are nonzero. -/
theorem claim48840_contact_distance_strict_iff
    {ι V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {x w : ι → V} {i j : ι} {t : ℝ}
    (hbase : ‖x i - x j‖ ^ 2 = 1)
    (hflex : inner ℝ (x i - x j) (w i - w j) = 0) :
    1 < ‖(x i + t • w i) - (x j + t • w j)‖ ↔
      t ≠ 0 ∧ w i ≠ w j := by
  have hexp := claim48840_contact_expansion (t := t) hbase hflex
  constructor
  · intro hstrict
    have hprod : 0 < t ^ 2 * ‖w i - w j‖ ^ 2 := by
      have hnorm : 0 ≤ ‖(x i + t • w i) - (x j + t • w j)‖ := norm_nonneg _
      nlinarith
    constructor
    · intro ht
      rw [ht] at hprod
      simp at hprod
    · intro hvel
      rw [hvel] at hprod
      simp at hprod
  · rintro ⟨ht, hvel⟩
    have hvel' : 0 < ‖w i - w j‖ ^ 2 := by
      exact sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hvel))
    have ht' : 0 < t ^ 2 := sq_pos_of_ne_zero ht
    have hprod : 0 < t ^ 2 * ‖w i - w j‖ ^ 2 := mul_pos ht' hvel'
    have hnorm : 0 ≤ ‖(x i + t • w i) - (x j + t • w j)‖ := norm_nonneg _
    nlinarith [hexp]

/-- Pinned diameter endpoints do not move, so their distance is unchanged. -/
theorem claim48840_diameter_pair_fixed
    {ι V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {x w : ι → V} {B : Finset ι} {i j : ι} {t : ℝ}
    (hpin : EndpointPinned B w) (hi : i ∈ B) (hj : j ∈ B) :
    ‖(x i + t • w i) - (x j + t • w j)‖ = ‖x i - x j‖ := by
  simp [hpin i hi, hpin j hj]

end MathlibPlus.Geometry
