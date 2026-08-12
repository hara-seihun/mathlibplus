import Mathlib

open scoped BigOperators
open Finset

namespace MathlibPlus.Analysis.ConditionalBetaMoments

/-!
Claim 53201 (`R-4192`): exact finite beta-Bernoulli moment arithmetic.
The finite average over `s = 0, ..., m` is the source's expectation over the
uniform count statistic `S_m`.
-/

lemma sum_range_id_rat (n : ℕ) :
    (∑ i ∈ range n, (i : ℚ)) =
      (n : ℚ) * ((n : ℚ) - 1) / 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [sum_range_succ, ih]
      push_cast
      ring

lemma sum_range_sq_rat (n : ℕ) :
    (∑ i ∈ range n, (i : ℚ) ^ 2) =
      (n : ℚ) * ((n : ℚ) - 1) * (2 * (n : ℚ) - 1) / 6 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [sum_range_succ, ih]
      push_cast
      ring

lemma sum_posterior_numerator (m : ℕ) :
    (∑ s ∈ range (m + 1),
      ((s + 1 : ℕ) : ℚ) * ((m - s + 1 : ℕ) : ℚ)) =
      ((m + 1 : ℕ) : ℚ) * ((m + 2 : ℕ) : ℚ) * ((m + 3 : ℕ) : ℚ) / 6 := by
  calc
    (∑ s ∈ range (m + 1),
        ((s + 1 : ℕ) : ℚ) * ((m - s + 1 : ℕ) : ℚ)) =
        ∑ s ∈ range (m + 1),
          ((s : ℚ) + 1) * ((m : ℚ) + 1 - (s : ℚ)) := by
            apply sum_congr rfl
            intro s hs
            have hsle : s ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hs)
            rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub hsle]
            push_cast
            ring
    _ = ∑ s ∈ range (m + 1),
          ((m : ℚ) * (s : ℚ) + (m : ℚ) + 1 - (s : ℚ) ^ 2) := by
            apply sum_congr rfl
            intro s hs
            ring
    _ = ((m + 1 : ℕ) : ℚ) * ((m + 2 : ℕ) : ℚ) *
          ((m + 3 : ℕ) : ℚ) / 6 := by
            rw [sum_sub_distrib, sum_add_distrib]
            rw [sum_add_distrib]
            rw [← Finset.mul_sum]
            simp only [sum_const, card_range, Nat.cast_add, Nat.cast_one]
            rw [sum_range_id_rat, sum_range_sq_rat]
            push_cast
            ring

/-- The two conditional beta moment averages from claim 53201. -/
theorem beta_moment_averages_claim53201 (m : ℕ) :
    (1 / ((m + 1 : ℕ) : ℚ)) *
        (∑ s ∈ range (m + 1),
          (((s + 1 : ℕ) : ℚ) * ((m - s + 1 : ℕ) : ℚ)) /
            (((m + 2 : ℕ) : ℚ) ^ 2 * ((m + 3 : ℕ) : ℚ))) =
      1 / (6 * ((m + 2 : ℕ) : ℚ)) ∧
    (1 / ((m + 1 : ℕ) : ℚ)) *
        (∑ s ∈ range (m + 1),
          (((s + 1 : ℕ) : ℚ) * ((m - s + 1 : ℕ) : ℚ)) /
            (((m + 2 : ℕ) : ℚ) * ((m + 3 : ℕ) : ℚ))) =
      1 / 6 := by
  rw [← Finset.sum_div, ← Finset.sum_div]
  rw [sum_posterior_numerator]
  constructor <;> field_simp <;> ring

/-- The expected conditional variance of the remaining normalized sum. -/
theorem stage_variance_formula_claim53201 (n m : ℕ) (hm : m < n) :
    let posteriorVariance : ℕ → ℕ → ℚ := fun m s ↦
      (((s + 1 : ℕ) : ℚ) * ((m - s + 1 : ℕ) : ℚ)) /
        (((m + 2 : ℕ) : ℚ) ^ 2 * ((m + 3 : ℕ) : ℚ))
    let posteriorBernoulliVariance : ℕ → ℕ → ℚ := fun m s ↦
      (((s + 1 : ℕ) : ℚ) * ((m - s + 1 : ℕ) : ℚ)) /
        (((m + 2 : ℕ) : ℚ) * ((m + 3 : ℕ) : ℚ))
    (1 / ((m + 1 : ℕ) : ℚ)) *
        (∑ s ∈ range (m + 1),
          4 / ((n : ℕ) : ℚ) ^ 2 *
            (((n - m : ℕ) : ℚ) * posteriorBernoulliVariance m s +
              (((n - m : ℕ) : ℚ) ^ 2) * posteriorVariance m s)) =
      2 * ((n + 2 : ℕ) : ℚ) * ((n - m : ℕ) : ℚ) /
        (3 * ((n : ℕ) : ℚ) ^ 2 * ((m + 2 : ℕ) : ℚ)) := by
  dsimp
  have hn : (n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hm))
  have hmn : ((n - m : ℕ) : ℚ) = (n : ℚ) - (m : ℚ) := by
    rw [Nat.cast_sub (Nat.le_of_lt hm)]
  have havg := beta_moment_averages_claim53201 m
  simp_rw [div_eq_mul_inv, mul_add]
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  rw [← Finset.mul_sum]
  rw [← Finset.mul_sum]
  rw [← Finset.mul_sum]
  have h1 :
      (1 / ((m + 1 : ℕ) : ℚ)) *
          (∑ s ∈ range (m + 1),
            (((s + 1 : ℕ) : ℚ) * ((m - s + 1 : ℕ) : ℚ)) *
              (((m + 2 : ℕ) : ℚ) ^ 2 * ((m + 3 : ℕ) : ℚ))⁻¹) =
        1 / (6 * ((m + 2 : ℕ) : ℚ)) := by
    simpa [div_eq_mul_inv] using havg.1
  have h2 :
      (1 / ((m + 1 : ℕ) : ℚ)) *
          (∑ s ∈ range (m + 1),
            (((s + 1 : ℕ) : ℚ) * ((m - s + 1 : ℕ) : ℚ)) *
              (((m + 2 : ℕ) : ℚ) * ((m + 3 : ℕ) : ℚ))⁻¹) =
        1 / 6 := by
    simpa [div_eq_mul_inv] using havg.2
  calc
    _ = 4 * ((n : ℚ) ^ 2)⁻¹ * ((n - m : ℕ) : ℚ) *
          (1 / ((m + 1 : ℕ) : ℚ) *
            (∑ s ∈ range (m + 1),
              (((s + 1 : ℕ) : ℚ) * ((m - s + 1 : ℕ) : ℚ)) *
                (((m + 2 : ℕ) : ℚ) * ((m + 3 : ℕ) : ℚ))⁻¹)) +
        4 * ((n : ℚ) ^ 2)⁻¹ * (((n - m : ℕ) : ℚ) ^ 2) *
          (1 / ((m + 1 : ℕ) : ℚ) *
            (∑ s ∈ range (m + 1),
              (((s + 1 : ℕ) : ℚ) * ((m - s + 1 : ℕ) : ℚ)) *
                (((m + 2 : ℕ) : ℚ) ^ 2 * ((m + 3 : ℕ) : ℚ))⁻¹)) := by ring
    _ = 4 * ((n : ℚ) ^ 2)⁻¹ * ((n - m : ℕ) : ℚ) * (1 / 6) +
        4 * ((n : ℚ) ^ 2)⁻¹ * (((n - m : ℕ) : ℚ) ^ 2) *
          (1 / (6 * ((m + 2 : ℕ) : ℚ))) := by rw [h2, h1]
    _ = 2 * ((n + 2 : ℕ) : ℚ) * ((n - m : ℕ) : ℚ) /
        (3 * ((n : ℕ) : ℚ) ^ 2 * ((m + 2 : ℕ) : ℚ)) := by
      rw [hmn]
      push_cast
      field_simp [hn]
      ring

/-- The complete finite statement of claim 53201. -/
theorem conditionalBetaMomentsClaim53201 :
    ∀ n : ℕ, 0 < n → ∀ m : ℕ, m < n →
      let posteriorVariance : ℕ → ℕ → ℚ := fun m s ↦
        (((s + 1 : ℕ) : ℚ) * ((m - s + 1 : ℕ) : ℚ)) /
          (((m + 2 : ℕ) : ℚ) ^ 2 * ((m + 3 : ℕ) : ℚ))
      let posteriorBernoulliVariance : ℕ → ℕ → ℚ := fun m s ↦
        (((s + 1 : ℕ) : ℚ) * ((m - s + 1 : ℕ) : ℚ)) /
          (((m + 2 : ℕ) : ℚ) * ((m + 3 : ℕ) : ℚ))
      (1 / ((m + 1 : ℕ) : ℚ)) *
            (∑ s ∈ range (m + 1), posteriorVariance m s) =
          1 / (6 * ((m + 2 : ℕ) : ℚ)) ∧
        (1 / ((m + 1 : ℕ) : ℚ)) *
            (∑ s ∈ range (m + 1), posteriorBernoulliVariance m s) =
          1 / 6 ∧
        (1 / ((m + 1 : ℕ) : ℚ)) *
            (∑ s ∈ range (m + 1),
              4 / ((n : ℕ) : ℚ) ^ 2 *
                (((n - m : ℕ) : ℚ) * posteriorBernoulliVariance m s +
                  (((n - m : ℕ) : ℚ) ^ 2) * posteriorVariance m s)) =
          2 * ((n + 2 : ℕ) : ℚ) * ((n - m : ℕ) : ℚ) /
            (3 * ((n : ℕ) : ℚ) ^ 2 * ((m + 2 : ℕ) : ℚ)) := by
  intro n hn m hm
  dsimp
  exact ⟨(beta_moment_averages_claim53201 m).1,
    (beta_moment_averages_claim53201 m).2,
    stage_variance_formula_claim53201 n m hm⟩

end MathlibPlus.Analysis.ConditionalBetaMoments
