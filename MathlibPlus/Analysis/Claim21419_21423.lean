import Mathlib

open Set MeasureTheory
namespace MathlibPlus.Analysis.Claim21419_21423

noncomputable def peanoKernel (r : ℕ) (u : ℝ) : ℝ :=
  (1 / 2 : ℝ) * max ((r : ℝ) + 1 / 2 - |u|) 0 ^ 2 -
    ((r : ℝ) + 1 / 2) * max (1 / 2 - |u|) 0 ^ 2

lemma peanoKernel_continuous (r : ℕ) : Continuous (peanoKernel r) := by
  unfold peanoKernel
  fun_prop

theorem peanoKernel_even_claim21420 (r : ℕ) (u : ℝ) : peanoKernel r (-u) = peanoKernel r u := by
  simp [peanoKernel, abs_neg]

lemma peanoKernel_eq_central_claim21420 {r : ℕ} {u : ℝ} (hu : |u| ≤ (1 / 2 : ℝ)) :
    peanoKernel r u = (r : ℝ)^2 / 2 + (r : ℝ) / 4 - (r : ℝ) * u^2 := by
  unfold peanoKernel
  have hr : (0 : ℝ) ≤ r := by positivity
  have hR : (0 : ℝ) ≤ (r : ℝ) + 1 / 2 - |u| := by linarith
  have hhalf : (0 : ℝ) ≤ 1 / 2 - |u| := by linarith
  rw [max_eq_left hR, max_eq_left hhalf]
  ring_nf
  rw [sq_abs]

lemma peanoKernel_eq_outer_claim21420 {r : ℕ} {u : ℝ}
    (hu₁ : (1 / 2 : ℝ) ≤ |u|) (hu₂ : |u| ≤ (r : ℝ) + 1 / 2) :
    peanoKernel r u = (1 / 2 : ℝ) * ((r : ℝ) + 1 / 2 - |u|)^2 := by
  unfold peanoKernel
  have hR : (0 : ℝ) ≤ (r : ℝ) + 1 / 2 - |u| := by linarith
  have hhalf : 1 / 2 - |u| ≤ (0 : ℝ) := by linarith
  rw [max_eq_left hR, max_eq_right hhalf]
  ring

lemma peanoKernel_eq_zero_claim21420 {r : ℕ} {u : ℝ}
    (hu : (r : ℝ) + 1 / 2 ≤ |u|) : peanoKernel r u = 0 := by
  unfold peanoKernel
  have hR : (r : ℝ) + 1 / 2 - |u| ≤ (0 : ℝ) := by linarith
  have hhalf : 1 / 2 - |u| ≤ (0 : ℝ) := by
    have hr : (0 : ℝ) ≤ r := by positivity
    linarith
  rw [max_eq_right hR, max_eq_right hhalf]
  ring

lemma peanoKernel_nonneg_claim21420 (r : ℕ) (u : ℝ) : 0 ≤ peanoKernel r u := by
  by_cases hu : |u| ≤ (1 / 2 : ℝ)
  · rw [peanoKernel_eq_central_claim21420 hu]
    have hr : (0 : ℝ) ≤ r := by positivity
    have hprod : |u| * (|u| - (1 / 2 : ℝ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (abs_nonneg u) (sub_nonpos.mpr hu)
    have hu2 : u ^ 2 ≤ (1 / 2 : ℝ)^2 := by
      nlinarith [sq_abs u, hprod]
    have hmul : 0 ≤ (r : ℝ) * ((1 / 2 : ℝ)^2 - u^2) :=
      mul_nonneg hr (by nlinarith)
    nlinarith [sq_nonneg (r : ℝ)]
  · have hu' : (1 / 2 : ℝ) ≤ |u| := le_of_not_ge hu
    by_cases hR : |u| ≤ (r : ℝ) + 1 / 2
    · rw [peanoKernel_eq_outer_claim21420 hu' hR]
      positivity
    · rw [peanoKernel_eq_zero_claim21420 (le_of_not_ge hR)]

theorem peanoKernel_support_claim21420 {r : ℕ} {u : ℝ}
    (hu : u ∈ Function.support (peanoKernel r)) :
    u ∈ Set.Icc (-(r : ℝ) - 1 / 2) ((r : ℝ) + 1 / 2) := by
  have hne : peanoKernel r u ≠ 0 := hu
  have habs : |u| < (r : ℝ) + 1 / 2 := by
    by_contra h
    exact hne (peanoKernel_eq_zero_claim21420 (le_of_not_gt h))
  constructor
  · by_cases hnonneg : 0 ≤ u
    · have hr : (0 : ℝ) ≤ r := by positivity
      linarith
    · rw [abs_of_nonpos (le_of_not_ge hnonneg)] at habs
      linarith
  · linarith [le_abs_self u]

theorem peanoKernel_central_lower_bound_claim21420 {r : ℕ} {u : ℝ}
    (hu : |u| ≤ (1 / 2 : ℝ)) :
    (r : ℝ)^2 / 2 ≤ peanoKernel r u := by
  rw [peanoKernel_eq_central_claim21420 hu]
  have hr : (0 : ℝ) ≤ r := by positivity
  have hprod : |u| * (|u| - (1 / 2 : ℝ)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (abs_nonneg u) (sub_nonpos.mpr hu)
  have hu2 : u ^ 2 ≤ (1 / 2 : ℝ)^2 := by
    nlinarith [sq_abs u, hprod]
  nlinarith [sq_nonneg (r : ℝ)]

theorem peanoKernel_mass_claim21421 (r : ℕ) :
    ∫ u : ℝ, peanoKernel r u = (r : ℝ) * ((r : ℝ) + 1) * (2 * (r : ℝ) + 1) / 6 := by
  let B : ℝ := (r : ℝ) + 1
  let A : ℝ := (r : ℝ) + 1 / 2
  let R : ℝ := (r : ℝ) + 1 / 2
  have hcont : Continuous (peanoKernel r) := peanoKernel_continuous r
  have hsupport : Function.support (peanoKernel r) ⊆ Set.Ioc (-B) B := by
    intro u hu
    have h := peanoKernel_support_claim21420 hu
    dsimp [B] at *
    constructor <;> linarith [h.1, h.2]
  have hzero_left : ∀ u ∈ Set.Icc (-B) (-A), peanoKernel r u = 0 := by
    intro u hu
    apply peanoKernel_eq_zero_claim21420
    have hnonpos : u ≤ 0 := by
      dsimp [A, B] at *
      linarith [hu.2]
    rw [abs_of_nonpos hnonpos]
    dsimp [A] at *
    linarith [hu.2]
  have houter_left : ∀ u ∈ Set.Icc (-A) (-1 / 2),
      peanoKernel r u = (1 / 2 : ℝ) * (R + u)^2 := by
    intro u hu
    have hnonpos : u ≤ 0 := by linarith [hu.2]
    have hupper : (1 / 2 : ℝ) ≤ |u| := by
      rw [abs_of_nonpos hnonpos]
      linarith [hu.2]
    have hlower : |u| ≤ (r : ℝ) + 1 / 2 := by
      rw [abs_of_nonpos hnonpos]
      dsimp [A] at *
      linarith [hu.1]
    rw [peanoKernel_eq_outer_claim21420 hupper hlower, abs_of_nonpos hnonpos]
    dsimp [R]
    ring
  have hcentral : ∀ u ∈ Set.Icc (-1 / 2) (1 / 2),
      peanoKernel r u = (r : ℝ)^2 / 2 + (r : ℝ) / 4 - (r : ℝ) * u^2 := by
    intro u hu
    apply peanoKernel_eq_central_claim21420
    have hu' : -(1 / 2 : ℝ) ≤ u ∧ u ≤ (1 / 2 : ℝ) := by
      constructor <;> linarith [hu.1, hu.2]
    exact (abs_le).2 hu'
  have houter_right : ∀ u ∈ Set.Icc (1 / 2) A,
      peanoKernel r u = (1 / 2 : ℝ) * (R - u)^2 := by
    intro u hu
    have hnonneg : 0 ≤ u := by linarith [hu.1]
    have hlower : (1 / 2 : ℝ) ≤ |u| := by
      rw [abs_of_nonneg hnonneg]
      exact hu.1
    have hupper : |u| ≤ (r : ℝ) + 1 / 2 := by
      rw [abs_of_nonneg hnonneg]
      dsimp [A] at *
      linarith [hu.2]
    rw [peanoKernel_eq_outer_claim21420 hlower hupper, abs_of_nonneg hnonneg]
  have hzero_right : ∀ u ∈ Set.Icc A B, peanoKernel r u = 0 := by
    intro u hu
    apply peanoKernel_eq_zero_claim21420
    have hnonneg : 0 ≤ u := by
      dsimp [A, B] at *
      linarith [hu.1]
    rw [abs_of_nonneg hnonneg]
    dsimp [A] at *
    linarith [hu.1]
  have hsplit (a b c : ℝ) :
      (∫ x : ℝ in a..b, peanoKernel r x) + ∫ x : ℝ in b..c, peanoKernel r x =
        ∫ x : ℝ in a..c, peanoKernel r x :=
    intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable a b) (hcont.intervalIntegrable b c)
  have hzeroL : (∫ x : ℝ in -B..-A, peanoKernel r x) = 0 := by
    rw [← intervalIntegral.integral_zero]
    apply intervalIntegral.integral_congr
    intro x hx
    have hle : -B ≤ -A := by
      dsimp [A, B]
      linarith
    have hx' : x ∈ Set.Icc (-B) (-A) := by
      simpa [uIcc_of_le hle] using hx
    exact hzero_left x hx'
  have houterL : (∫ x : ℝ in -A..(-1 / 2 : ℝ), peanoKernel r x) =
      ∫ x : ℝ in -A..(-1 / 2 : ℝ), (1 / 2 : ℝ) * (R + x)^2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le] at hx
    · exact houter_left x hx
    · dsimp [A]
      linarith
  have hcentralI : (∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ), peanoKernel r x) =
      ∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        (r : ℝ)^2 / 2 + (r : ℝ) / 4 - (r : ℝ) * x^2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le] at hx
    · exact hcentral x hx
    · norm_num
  have houterR : (∫ x : ℝ in (1 / 2 : ℝ)..A, peanoKernel r x) =
      ∫ x : ℝ in (1 / 2 : ℝ)..A, (1 / 2 : ℝ) * (R - x)^2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le] at hx
    · exact houter_right x hx
    · dsimp [A]
      linarith
  have hzeroR : (∫ x : ℝ in A..B, peanoKernel r x) = 0 := by
    rw [← intervalIntegral.integral_zero]
    apply intervalIntegral.integral_congr
    intro x hx
    have hle : A ≤ B := by
      dsimp [A, B]
      linarith
    have hx' : x ∈ Set.Icc A B := by
      simpa [uIcc_of_le hle] using hx
    exact hzero_right x hx'
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hsupport]
  rw [← hsplit (-B) (-A) B, ← hsplit (-A) (-1 / 2) B,
    ← hsplit (-1 / 2) (1 / 2) B, ← hsplit (1 / 2) A B]
  rw [hzeroL, houterL, hcentralI, houterR, hzeroR]
  have houterLcalc :
      (∫ x : ℝ in -A..(-1 / 2 : ℝ), (1 / 2 : ℝ) * (R + x)^2) =
        (r : ℝ)^3 / 6 := by
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_comp_add_left (fun y : ℝ => y^2) R]
    dsimp [A, R]
    norm_num [integral_pow]
    ring
  have houterRcalc :
      (∫ x : ℝ in (1 / 2 : ℝ)..A, (1 / 2 : ℝ) * (R - x)^2) =
        (r : ℝ)^3 / 6 := by
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_comp_sub_left (fun y : ℝ => y^2) R]
    dsimp [A, R]
    norm_num [integral_pow]
    ring
  rw [houterLcalc, houterRcalc]
  have hC : IntervalIntegrable
      (fun _ : ℝ => (r : ℝ)^2 / 2 + (r : ℝ) / 4) volume (-1 / 2) (1 / 2) :=
    continuous_const.intervalIntegrable _ _
  have hQ : IntervalIntegrable
      (fun x : ℝ => (r : ℝ) * x^2) volume (-1 / 2) (1 / 2) :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hC hQ]
  have hC1 : IntervalIntegrable
      (fun _ : ℝ => (r : ℝ)^2 / 2) volume (-1 / 2) (1 / 2) :=
    continuous_const.intervalIntegrable _ _
  have hC2 : IntervalIntegrable
      (fun _ : ℝ => (r : ℝ) / 4) volume (-1 / 2) (1 / 2) :=
    continuous_const.intervalIntegrable _ _
  rw [intervalIntegral.integral_add hC1 hC2]
  simp [integral_pow]
  ring

end MathlibPlus.Analysis.Claim21419_21423
