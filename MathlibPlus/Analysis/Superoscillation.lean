import Mathlib

/-!
# Finite-difference arithmetic for endpoint-local superoscillation

This module formalizes the self-contained finite combinatorics and scalar threshold
from packet `C-0242`.  It does not introduce a placeholder complex-measure Fourier
transform or claim the packet's open front-to-sample transfer.
-/

open scoped BigOperators

namespace MathlibPlus.Analysis.Superoscillation

/-- The exact first assertion of Record 4: the `n`th forward-difference functional
has magnitude `2^n ‖a‖` on the alternating samples `a(-1)^j`. -/
theorem alternatingDifferenceMagnitude (a : ℂ) (n : ℕ) :
    ‖(∑ j ∈ Finset.range (n + 1),
      (-1 : ℂ) ^ (n - j) * (Nat.choose n j) * (a * (-1 : ℂ) ^ j))‖ =
      (2 : ℝ) ^ n * ‖a‖ := by
  have hsummand : ∀ j ∈ Finset.range (n + 1),
      (-1 : ℂ) ^ (n - j) * (Nat.choose n j) * (a * (-1 : ℂ) ^ j) =
        ((-1 : ℂ) ^ n * a) * (Nat.choose n j) := by
    intro j hj
    have hjn : j ≤ n := by simpa [Finset.mem_range] using hj
    have hp : (-1 : ℂ) ^ (n - j) * (-1 : ℂ) ^ j = (-1 : ℂ) ^ n := by
      rw [← pow_add, Nat.sub_add_cancel hjn]
    calc
      (-1 : ℂ) ^ (n - j) * (Nat.choose n j) * (a * (-1 : ℂ) ^ j) =
          ((-1 : ℂ) ^ (n - j) * (-1 : ℂ) ^ j) * a * (Nat.choose n j) := by
            ring
      _ = ((-1 : ℂ) ^ n * a) * (Nat.choose n j) := by rw [hp]
  rw [Finset.sum_congr rfl hsummand]
  rw [← Finset.mul_sum]
  rw [← Nat.cast_sum, Nat.sum_range_choose]
  simp [norm_pow, mul_comm]

/-- The error-amplification assertion of Record 4.  No independence or phase
hypothesis is added: only the packet's pointwise sample-error bounds are used. -/
theorem alternatingDifferenceErrorBound (e : ℕ → ℂ) (a : ℂ) (η : ℝ) (n : ℕ)
    (_hη : 0 ≤ η) (herr : ∀ j ≤ n, ‖e j‖ ≤ η * ‖a‖) :
    ‖(∑ j ∈ Finset.range (n + 1),
      (-1 : ℂ) ^ (n - j) * (Nat.choose n j) * e j)‖ ≤
      η * (2 : ℝ) ^ n * ‖a‖ := by
  calc
    ‖(∑ j ∈ Finset.range (n + 1),
      (-1 : ℂ) ^ (n - j) * (Nat.choose n j) * e j)‖ ≤
        ∑ j ∈ Finset.range (n + 1),
          ‖(-1 : ℂ) ^ (n - j) * (Nat.choose n j) * e j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (n + 1),
          (Nat.choose n j : ℝ) * (η * ‖a‖) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn : j ≤ n := by simpa [Finset.mem_range] using hj
      calc
        ‖(-1 : ℂ) ^ (n - j) * (Nat.choose n j) * e j‖ =
            (Nat.choose n j : ℝ) * ‖e j‖ := by simp
        _ ≤ (Nat.choose n j : ℝ) * (η * ‖a‖) :=
          mul_le_mul_of_nonneg_left (herr j hjn) (by positivity)
    _ = η * (2 : ℝ) ^ n * ‖a‖ := by
      rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      norm_num
      ring

/-- The complete lower-bound conclusion of Record 4: samples lying within relative
error `η` of the alternating target force the displayed difference magnitude. -/
theorem alternatingSamplesLowerBound (sample : ℕ → ℂ) (a : ℂ) (η : ℝ) (n : ℕ)
    (hη : 0 ≤ η)
    (hsample : ∀ j ≤ n, ‖sample j - a * (-1 : ℂ) ^ j‖ ≤ η * ‖a‖) :
    (1 - η) * (2 : ℝ) ^ n * ‖a‖ ≤
      ‖(∑ j ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ (n - j) * (Nat.choose n j) * sample j)‖ := by
  let B : ℂ := ∑ j ∈ Finset.range (n + 1),
    (-1 : ℂ) ^ (n - j) * (Nat.choose n j) * sample j
  let T : ℂ := ∑ j ∈ Finset.range (n + 1),
    (-1 : ℂ) ^ (n - j) * (Nat.choose n j) * (a * (-1 : ℂ) ^ j)
  have herror := alternatingDifferenceErrorBound
    (fun j => sample j - a * (-1 : ℂ) ^ j) a η n hη hsample
  have hBT : B - T = ∑ j ∈ Finset.range (n + 1),
      (-1 : ℂ) ^ (n - j) * (Nat.choose n j) *
        (sample j - a * (-1 : ℂ) ^ j) := by
    simp only [B, T, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hdiff : ‖B - T‖ ≤ η * (2 : ℝ) ^ n * ‖a‖ := by
    rw [hBT]
    exact herror
  have hT : ‖T‖ = (2 : ℝ) ^ n * ‖a‖ := by
    simpa [T] using alternatingDifferenceMagnitude a n
  have htri : ‖T‖ ≤ ‖B‖ + ‖B - T‖ := by
    calc
      ‖T‖ = ‖B - (B - T)‖ := by
        congr 1
        ring
      _ ≤ ‖B‖ + ‖B - T‖ := norm_sub_le _ _
  rw [hT] at htri
  change (1 - η) * (2 : ℝ) ^ n * ‖a‖ ≤ ‖B‖
  nlinarith

/-- Record 7's exact base threshold.  The positive-`L` hypothesis is retained even
though positivity of the denominator only needs `r > 0`. -/
theorem superoscillationBase_gt_one (L r : ℝ) (_hL : 0 < L) (hr : 0 < r) :
    (1 < 2 * L / (Real.pi * r) ↔ Real.pi * r < 2 * L) := by
  have hden : 0 < Real.pi * r := mul_pos Real.pi_pos hr
  simpa using (lt_div_iff₀ hden : 1 < 2 * L / (Real.pi * r) ↔ _)

end MathlibPlus.Analysis.Superoscillation
