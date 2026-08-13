import Mathlib

namespace MathlibPlus.Analysis.Claim21800

open Filter
open _root_.Asymptotics

private lemma rpow_three_two (j : ℕ) :
    (((j : ℝ) / 3) ^ 3) ^ (2 / 3 : ℝ) = ((j : ℝ) / 3) ^ 2 := by
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by positivity)]
  norm_num

private lemma rpow_one_three (j : ℕ) :
    (((j : ℝ) / 3) ^ 3) ^ (1 / 3 : ℝ) = ((j : ℝ) / 3) := by
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by positivity)]
  norm_num

/-- Claim 21800: the two consecutive endpoint displacements have the displayed
quadratic formulas, and after subtracting the leading `T j ^ (2/3)` term each
is `O (T j ^ (1/3))` along the natural numbers. -/
theorem endpointDisplacements_and_asymptoticWidth_claim21800 :
    let T : ℕ → ℝ := fun j => ((j : ℝ) / 3) ^ 3
    let dPlus : ℕ → ℝ := fun j => (((j + 1 : ℕ) : ℝ) / 3) ^ 3 - T j
    let dMinus : ℕ → ℝ := fun j => T j - (((j - 1 : ℕ) : ℝ) / 3) ^ 3
    (∀ j : ℕ, dPlus j = (j : ℝ)^2 / 9 + (j : ℝ) / 9 + 1 / 27) ∧
      (∀ j : ℕ, 1 ≤ j →
        dMinus j = (j : ℝ)^2 / 9 - (j : ℝ) / 9 + 1 / 27) ∧
      (fun j : ℕ => dPlus j - (T j) ^ (2 / 3 : ℝ)) =O[atTop]
        (fun j : ℕ => (T j) ^ (1 / 3 : ℝ)) ∧
      (fun j : ℕ => dMinus j - (T j) ^ (2 / 3 : ℝ)) =O[atTop]
        (fun j : ℕ => (T j) ^ (1 / 3 : ℝ)) := by
  dsimp
  have hplus : ∀ j : ℕ,
      (((j + 1 : ℕ) : ℝ) / 3) ^ 3 - ((j : ℝ) / 3) ^ 3 =
        (j : ℝ)^2 / 9 + (j : ℝ) / 9 + 1 / 27 := by
    intro j
    norm_num [Nat.cast_add]
    ring
  have hminus : ∀ j : ℕ, 1 ≤ j →
      ((j : ℝ) / 3) ^ 3 - (((j - 1 : ℕ) : ℝ) / 3) ^ 3 =
        (j : ℝ)^2 / 9 - (j : ℝ) / 9 + 1 / 27 := by
    intro j hj
    have hcast : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hcast]
    ring
  refine ⟨hplus, hminus, ?_, ?_⟩
  · refine (Asymptotics.IsBigOWith.of_bound (c := 1) ?_).isBigO
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with j hj
    rw [rpow_three_two, rpow_one_three]
    rw [hplus]
    have hdiff : (j : ℝ)^2 / 9 + (j : ℝ) / 9 + 1 / 27 - ((j : ℝ) / 3) ^ 2 =
        (j : ℝ) / 9 + 1 / 27 := by ring
    rw [hdiff, Real.norm_eq_abs, Real.norm_eq_abs]
    have hright : 0 ≤ (j : ℝ) / 3 := by positivity
    have hjr : (3 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    rw [abs_of_nonneg hright]
    apply abs_le.mpr
    constructor <;> norm_num <;> linarith
  · refine (Asymptotics.IsBigOWith.of_bound (c := 1) ?_).isBigO
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with j hj
    rw [rpow_three_two, rpow_one_three]
    have hminus' := hminus j (by omega)
    rw [hminus']
    have hdiff : (j : ℝ)^2 / 9 - (j : ℝ) / 9 + 1 / 27 - ((j : ℝ) / 3) ^ 2 =
        -(j : ℝ) / 9 + 1 / 27 := by ring
    rw [hdiff, Real.norm_eq_abs, Real.norm_eq_abs]
    have hright : 0 ≤ (j : ℝ) / 3 := by positivity
    have hjr : (3 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    rw [abs_of_nonneg hright]
    apply abs_le.mpr
    constructor <;> norm_num <;> linarith

end MathlibPlus.Analysis.Claim21800
