import Mathlib

open Set

namespace MathlibPlus.Analysis.FirstShellFactors

private lemma firstShellQ2_pos {x : ℝ} (_hx : 3 ≤ x) :
    0 < 4 * x ^ 2 - 12 * x + 15 := by
  nlinarith [sq_nonneg (2 * x - 3)]

private lemma firstShellQ3_pos {x : ℝ} (hx : 3 ≤ x) :
    0 < 8 * x ^ 3 - 36 * x ^ 2 + 90 * x - 105 := by
  have hu : 0 ≤ x - 3 := by linarith
  have hu2 : 0 ≤ (x - 3) ^ 2 := sq_nonneg _
  have hu3 : 0 ≤ (x - 3) ^ 3 := pow_nonneg hu 3
  nlinarith

private lemma firstShellQ4_pos {x : ℝ} (hx : 3 ≤ x) :
    0 < 16 * x ^ 4 - 96 * x ^ 3 + 360 * x ^ 2 - 840 * x + 945 := by
  have hu : 0 ≤ x - 3 := by linarith
  have hu2 : 0 ≤ (x - 3) ^ 2 := sq_nonneg _
  have hu3 : 0 ≤ (x - 3) ^ 3 := pow_nonneg hu 3
  have hu4 : 0 ≤ (x - 3) ^ 4 := pow_nonneg hu 4
  nlinarith

private lemma firstShellQ2_strictMonoOn :
    StrictMonoOn (fun x : ℝ => 4 * x ^ 2 - 12 * x + 15) (Ici 3) := by
  intro x hx y hy hxy
  have hx3 : 3 ≤ x := hx
  have hy3 : 3 ≤ y := hy
  have hdiff : 0 <
      (4 * y ^ 2 - 12 * y + 15) - (4 * x ^ 2 - 12 * x + 15) := by
    have hfac :
        (4 * y ^ 2 - 12 * y + 15) - (4 * x ^ 2 - 12 * x + 15) =
          (y - x) * (4 * (x + y) - 12) := by ring
    rw [hfac]
    apply mul_pos (sub_pos.mpr hxy)
    nlinarith
  exact sub_pos.mp hdiff

private lemma firstShellQ3_strictMonoOn :
    StrictMonoOn (fun x : ℝ => 8 * x ^ 3 - 36 * x ^ 2 + 90 * x - 105) (Ici 3) := by
  intro x hx y hy hxy
  have hx3 : 3 ≤ x := hx
  have hy3 : 3 ≤ y := hy
  have hxy0 : 0 ≤ x - 3 := by linarith
  have hyy0 : 0 ≤ y - 3 := by linarith
  have hcross : 0 ≤ (x - 3) * (y - 3) := mul_nonneg hxy0 hyy0
  have hdiff : 0 <
      (8 * y ^ 3 - 36 * y ^ 2 + 90 * y - 105) -
        (8 * x ^ 3 - 36 * x ^ 2 + 90 * x - 105) := by
    have hfac :
        (8 * y ^ 3 - 36 * y ^ 2 + 90 * y - 105) -
            (8 * x ^ 3 - 36 * x ^ 2 + 90 * x - 105) =
          (y - x) * (8 * (x ^ 2 + x * y + y ^ 2) - 36 * (x + y) + 90) := by
      ring
    have hbracket : 0 < 8 * (x ^ 2 + x * y + y ^ 2) - 36 * (x + y) + 90 := by
      nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 3)]
    rw [hfac]
    exact mul_pos (sub_pos.mpr hxy) hbracket
  exact sub_pos.mp hdiff

private lemma firstShellQ4_strictMonoOn :
    StrictMonoOn
      (fun x : ℝ => 16 * x ^ 4 - 96 * x ^ 3 + 360 * x ^ 2 - 840 * x + 945)
      (Ici 3) := by
  intro x hx y hy hxy
  have hx3 : 3 ≤ x := hx
  have hy3 : 3 ≤ y := hy
  have hu : 0 ≤ x - 3 := by linarith
  have hv : 0 ≤ y - 3 := by linarith
  have hu2 : 0 ≤ (x - 3) ^ 2 := sq_nonneg _
  have hv2 : 0 ≤ (y - 3) ^ 2 := sq_nonneg _
  have hu3 : 0 ≤ (x - 3) ^ 3 := pow_nonneg hu 3
  have hv3 : 0 ≤ (y - 3) ^ 3 := pow_nonneg hv 3
  have hcross : 0 ≤ (x - 3) * (y - 3) := mul_nonneg hu hv
  have hcross2 : 0 ≤ (x - 3) * (y - 3) ^ 2 := mul_nonneg hu hv2
  have hcross3 : 0 ≤ (y - 3) * (x - 3) ^ 2 := mul_nonneg hv hu2
  have hdiff : 0 <
      (16 * y ^ 4 - 96 * y ^ 3 + 360 * y ^ 2 - 840 * y + 945) -
        (16 * x ^ 4 - 96 * x ^ 3 + 360 * x ^ 2 - 840 * x + 945) := by
    have hfac :
        (16 * y ^ 4 - 96 * y ^ 3 + 360 * y ^ 2 - 840 * y + 945) -
            (16 * x ^ 4 - 96 * x ^ 3 + 360 * x ^ 2 - 840 * x + 945) =
          (y - x) *
            (16 * (y ^ 3 + y ^ 2 * x + y * x ^ 2 + x ^ 3)
              - 96 * (y ^ 2 + y * x + x ^ 2) + 360 * (y + x) - 840) := by
      ring
    have hbracket : 0 <
        16 * (y ^ 3 + y ^ 2 * x + y * x ^ 2 + x ^ 3)
          - 96 * (y ^ 2 + y * x + x ^ 2) + 360 * (y + x) - 840 := by
      nlinarith
    rw [hfac]
    exact mul_pos (sub_pos.mpr hxy) hbracket
  exact sub_pos.mp hdiff

/-- Claim 3260: the three displayed first-shell factors are positive and
strictly increasing once `x` is at least `π exp (13/8)`.  The source uses
“increasing” without distinguishing strict from weak monotonicity; this
formalization records the stronger strict version on `Ici 3`. -/
theorem firstShellFactors_pos_and_strictMono
    (x : ℝ) (hx : Real.pi * Real.exp (13 / 8 : ℝ) ≤ x) :
    0 < 4 * x ^ 2 - 12 * x + 15 ∧
      0 < 8 * x ^ 3 - 36 * x ^ 2 + 90 * x - 105 ∧
      0 < 16 * x ^ 4 - 96 * x ^ 3 + 360 * x ^ 2 - 840 * x + 945 ∧
      StrictMonoOn (fun x : ℝ => 4 * x ^ 2 - 12 * x + 15) (Ici 3) ∧
      StrictMonoOn (fun x : ℝ => 8 * x ^ 3 - 36 * x ^ 2 + 90 * x - 105) (Ici 3) ∧
      StrictMonoOn
        (fun x : ℝ => 16 * x ^ 4 - 96 * x ^ 3 + 360 * x ^ 2 - 840 * x + 945)
        (Ici 3) := by
  have hexp : 1 ≤ Real.exp (13 / 8 : ℝ) := by
    apply Real.one_le_exp
    norm_num
  have hpi : 0 < Real.pi := Real.pi_pos
  have hprod : 0 ≤ Real.pi * (Real.exp (13 / 8 : ℝ) - 1) :=
    mul_nonneg hpi.le (sub_nonneg.mpr hexp)
  have hthreshold : 3 ≤ Real.pi * Real.exp (13 / 8 : ℝ) := by
    nlinarith [Real.pi_gt_three]
  have hx3 : 3 ≤ x := hthreshold.trans hx
  exact ⟨firstShellQ2_pos hx3, firstShellQ3_pos hx3, firstShellQ4_pos hx3,
    firstShellQ2_strictMonoOn, firstShellQ3_strictMonoOn, firstShellQ4_strictMonoOn⟩

end MathlibPlus.Analysis.FirstShellFactors
