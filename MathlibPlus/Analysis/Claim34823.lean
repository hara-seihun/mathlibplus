import Mathlib

open scoped BigOperators

namespace MathlibPlus.Analysis.Claim34823

/-- The equality-profile recurrence from R-1904, expressed as a formal
exponential generating function over `ℚ`. -/
theorem exponentialGeneratingFunction_recurrence_claim34823
    (U : ℕ → ℚ)
    (h0 : U 0 = 1)
    (hrec : ∀ n, 0 < n →
      U n = ∑ r ∈ Finset.range n, (Nat.choose n r : ℚ) * U r) :
    let E : PowerSeries ℚ :=
      PowerSeries.mk (fun n => U n / (Nat.factorial n : ℚ))
    PowerSeries.exp ℚ * E = (2 : ℚ) • E - 1 := by
  dsimp
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_mul, PowerSeries.coeff_exp, PowerSeries.coeff_mk,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [map_sub, PowerSeries.coeff_smul, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  cases n with
  | zero =>
      norm_num [h0]
  | succ n =>
      rw [if_neg (Nat.succ_ne_zero n)]
      have hfactor (N j : ℕ) (hj : j ≤ N) :
          ((1 : ℚ) / (j.factorial : ℚ)) *
              (1 / ((N - j).factorial : ℚ)) =
            (N.choose j : ℚ) / (N.factorial : ℚ) := by
        field_simp
        norm_cast
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (Nat.choose_mul_factorial_mul_factorial hj).symm
      have hterm (j : ℕ) (hj : j ≤ n + 1) :
          ((1 : ℚ) / (j.factorial : ℚ)) *
              (U (n + 1 - j) / ((n + 1 - j).factorial : ℚ)) =
            ((n + 1).choose j : ℚ) * U (n + 1 - j) /
              (n + 1).factorial := by
        calc
          _ = (((1 : ℚ) / (j.factorial : ℚ)) *
              (1 / ((n + 1 - j).factorial : ℚ))) * U (n + 1 - j) := by ring
          _ = ((n + 1).choose j : ℚ) /
              (n + 1).factorial * U (n + 1 - j) := by
            rw [hfactor (n + 1) j hj]
          _ = _ := by ring
      rw [Finset.sum_range_succ']
      have htail :
          (∑ x ∈ Finset.range (n + 1),
              (algebraMap ℚ ℚ) (1 / ↑(x + 1).factorial) *
                (U (n + 1 - (x + 1)) /
                  ↑(n + 1 - (x + 1)).factorial)) =
            ∑ r ∈ Finset.range (n + 1),
              ((n + 1).choose r : ℚ) * U r /
                (n + 1).factorial := by
        calc
          _ = ∑ x ∈ Finset.range (n + 1),
                ((n + 1).choose (x + 1) : ℚ) *
                  U (n + 1 - (x + 1)) /
                    (n + 1).factorial := by
            apply Finset.sum_congr rfl
            intro x hx
            have hx' : x < n + 1 := Finset.mem_range.mp hx
            simpa using hterm (x + 1) (by omega)
          _ = ∑ x ∈ Finset.range (n + 1),
                ((n + 1).choose (n - x) : ℚ) * U (n - x) /
                  (n + 1).factorial := by
            apply Finset.sum_congr rfl
            intro x hx
            have hx' : x < n + 1 := Finset.mem_range.mp hx
            rw [← Nat.choose_symm (by omega)]
            simp only [Nat.succ_sub_succ_eq_sub]
          _ = ∑ r ∈ Finset.range (n + 1),
                ((n + 1).choose r : ℚ) * U r /
                  (n + 1).factorial := by
            simpa using (Finset.sum_range_reflect
              (fun r => ((n + 1).choose r : ℚ) * U r /
                (n + 1).factorial) (n + 1))
      rw [htail]
      simp only [Nat.zero_sub, Nat.sub_zero, Nat.add_zero, Nat.factorial_zero,
        Nat.cast_one, one_div, one_mul]
      have hrec' := hrec (n + 1) (by omega)
      rw [hrec']
      rw [Finset.sum_div]
      norm_num [Nat.sub_zero]
      ring

/-- The same recurrence gives the closed formal-series form
`E = (2 - exp X)⁻¹`; the inverse is well-defined because the denominator has
constant coefficient one. -/
theorem exponentialGeneratingFunction_closedForm_claim34823
    (U : ℕ → ℚ)
    (h0 : U 0 = 1)
    (hrec : ∀ n, 0 < n →
      U n = ∑ r ∈ Finset.range n, (Nat.choose n r : ℚ) * U r) :
    let E : PowerSeries ℚ :=
      PowerSeries.mk (fun n => U n / (Nat.factorial n : ℚ))
    E = ((2 : ℚ) • (1 : PowerSeries ℚ) - PowerSeries.exp ℚ)⁻¹ := by
  dsimp
  have hfun := exponentialGeneratingFunction_recurrence_claim34823 U h0 hrec
  let D : PowerSeries ℚ := (2 : ℚ) • (1 : PowerSeries ℚ) - PowerSeries.exp ℚ
  have hD : PowerSeries.constantCoeff D ≠ 0 := by
    dsimp [D]
    norm_num
  apply (PowerSeries.eq_inv_iff_mul_eq_one hD).2
  calc
    PowerSeries.mk (fun n => U n / (Nat.factorial n : ℚ)) * D =
        D * PowerSeries.mk (fun n => U n / (Nat.factorial n : ℚ)) := by
      ac_rfl
    _ = (2 : ℚ) • PowerSeries.mk (fun n => U n / (Nat.factorial n : ℚ)) -
        PowerSeries.exp ℚ * PowerSeries.mk (fun n => U n / (Nat.factorial n : ℚ)) := by
      dsimp [D]
      rw [sub_mul, smul_mul_assoc, one_mul]
    _ = 1 := by
      rw [hfun]
      ring

end MathlibPlus.Analysis.Claim34823
