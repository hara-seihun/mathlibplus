import Mathlib

namespace MathlibPlus.Analysis.HarmonicLogDivisor

/-- The harmonic number with the conventional summation index `1 ≤ k ≤ N`. -/
noncomputable def H (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (1 : ℝ) / ((k + 1 : ℕ) : ℝ)

/-- The logarithmic divisor sum with the conventional summation index
`1 ≤ k ≤ N`. -/
noncomputable def S (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N,
    Real.log ((k + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)

/-- The quantity `D_N` in claim 2206. -/
noncomputable def D (N : ℕ) : ℝ := H N * Real.log (N : ℝ) - 2 * S N

theorem D_one : D 1 = 0 := by
  simp [D, H, S]

theorem harmonic_le_H (N : ℕ) :
    Real.log ((N + 1 : ℕ) : ℝ) ≤ H N := by
  have hterm : ∀ i ∈ Finset.range N,
      Real.log ((i + 2 : ℕ) : ℝ) - Real.log ((i + 1 : ℕ) : ℝ) ≤
        (1 : ℝ) / ((i + 1 : ℕ) : ℝ) := by
    intro i hi
    have hpos1 : 0 < ((i + 1 : ℕ) : ℝ) := by positivity
    have hpos2 : 0 < ((i + 2 : ℕ) : ℝ) := by positivity
    have h := Real.log_le_sub_one_of_pos
      (x := ((i + 2 : ℕ) : ℝ) / ((i + 1 : ℕ) : ℝ))
      (div_pos hpos2 hpos1)
    calc
      Real.log ((i + 2 : ℕ) : ℝ) - Real.log ((i + 1 : ℕ) : ℝ) =
          Real.log (((i + 2 : ℕ) : ℝ) / ((i + 1 : ℕ) : ℝ)) := by
            rw [Real.log_div (ne_of_gt hpos2) (ne_of_gt hpos1)]
      _ ≤ ((i + 2 : ℕ) : ℝ) / ((i + 1 : ℕ) : ℝ) - 1 := h
      _ = (1 : ℝ) / ((i + 1 : ℕ) : ℝ) := by
        field_simp
        norm_num [Nat.cast_add, Nat.cast_one]
  have hs := Finset.sum_le_sum hterm
  have htel :
      (∑ i ∈ Finset.range N,
        (Real.log ((i + 2 : ℕ) : ℝ) - Real.log ((i + 1 : ℕ) : ℝ))) =
        Real.log ((N + 1 : ℕ) : ℝ) := by
    have h := Finset.sum_range_sub
      (fun i : ℕ => Real.log ((i + 1 : ℕ) : ℝ)) N
    simpa [Nat.add_assoc, Nat.cast_add, Nat.cast_one] using h
  rw [htel] at hs
  simpa [H] using hs

theorem log_increment_lower (N : ℕ) (hN : 1 ≤ N) :
    (1 : ℝ) / (N + 1 : ℝ) < Real.log (1 + 1 / (N : ℝ)) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have h := Real.lt_log_one_add_of_pos
    (x := (1 : ℝ) / N) (by positivity)
  calc
    (1 : ℝ) / (N + 1 : ℝ) <
        2 * ((1 : ℝ) / N) / ((1 : ℝ) / N + 2) := by
          field_simp
          nlinarith
    _ < Real.log (1 + 1 / (N : ℝ)) := h

theorem D_succ_sub (N : ℕ) (hN : 1 ≤ N) :
    D (N + 1) - D N =
      H N * Real.log (1 + 1 / (N : ℝ)) -
        Real.log ((N + 1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hNp1 : (N + 1 : ℝ) ≠ 0 := by positivity
  have hsumH : H (N + 1) = H N + (1 : ℝ) / (N + 1 : ℝ) := by
    unfold H
    rw [Finset.sum_range_succ]
    simp only [Nat.cast_add, Nat.cast_one]
  have hsumS : S (N + 1) = S N + Real.log (N + 1 : ℝ) / (N + 1 : ℝ) := by
    unfold S
    rw [Finset.sum_range_succ]
    simp only [Nat.cast_add, Nat.cast_one]
  unfold D
  rw [hsumH, hsumS]
  have hlog : Real.log (N + 1 : ℝ) - Real.log (N : ℝ) =
      Real.log (1 + 1 / (N : ℝ)) := by
    rw [← Real.log_div (by positivity) hN0]
    congr 1
    field_simp
  norm_num [Nat.cast_add, Nat.cast_one] at ⊢
  have hlog' : Real.log (↑N + 1) - Real.log ↑N =
      Real.log (1 + (N : ℝ)⁻¹) := by
    simpa [div_eq_mul_inv] using hlog
  linear_combination H N * hlog'

theorem D_succ_sub_pos (N : ℕ) (hN : 1 ≤ N) :
    0 < D (N + 1) - D N := by
  rw [D_succ_sub N hN]
  have hNpos : 0 < (N : ℝ) := by positivity
  have hNp1pos : 0 < (N + 1 : ℝ) := by positivity
  have hlogpos : 0 < Real.log ((N + 1 : ℕ) : ℝ) := by
    apply Real.log_pos
    norm_num [Nat.cast_add, Nat.cast_one]
    exact_mod_cast hN
  have hH : Real.log ((N + 1 : ℕ) : ℝ) ≤ H N := harmonic_le_H N
  have hinc : (1 : ℝ) / (N + 1 : ℝ) <
      Real.log (1 + 1 / (N : ℝ)) := log_increment_lower N hN
  have hprod : Real.log ((N + 1 : ℕ) : ℝ) / (N + 1 : ℝ) <
      Real.log ((N + 1 : ℕ) : ℝ) * Real.log (1 + 1 / (N : ℝ)) := by
    calc
      Real.log ((N + 1 : ℕ) : ℝ) / (N + 1 : ℝ) =
          Real.log ((N + 1 : ℕ) : ℝ) * (1 / (N + 1 : ℝ)) := by ring
      _ < Real.log ((N + 1 : ℕ) : ℝ) *
          Real.log (1 + 1 / (N : ℝ)) :=
        mul_lt_mul_of_pos_left hinc hlogpos
  have hincpos : 0 < Real.log (1 + 1 / (N : ℝ)) :=
    lt_trans (by positivity) hinc
  have hscale := mul_le_mul_of_nonneg_right hH (le_of_lt hincpos)
  apply sub_pos.mpr
  simpa [Nat.cast_add, Nat.cast_one, div_eq_mul_inv] using
    hprod.trans_le hscale

theorem D_nonneg (N : ℕ) (hN : 1 ≤ N) : 0 ≤ D N := by
  refine Nat.le_induction (m := 1) ?_ ?_ N hN
  · rw [D_one]
  · intro n hn ih
    have hp := D_succ_sub_pos n hn
    linarith

theorem final_bound (N : ℕ) (hN : 1 ≤ N) :
    2 * S N ≤ H N * Real.log (N : ℝ) := by
  have hd := D_nonneg N hN
  unfold D at hd
  linarith

end MathlibPlus.Analysis.HarmonicLogDivisor

namespace MathlibPlus.Open.Analysis.HarmonicLogDivisor

open MathlibPlus.Analysis.HarmonicLogDivisor

/-- Claim 2206.  The source notation `k ≤ N` is represented by the shifted
range `k = i + 1` with `i < N`, so the undefined `k = 0` term is not inserted.
-/
def harmonicLogDivisorPositivity : Prop :=
  D 1 = 0 ∧
  (∀ (N : ℕ), 1 ≤ N →
    D (N + 1) - D N =
      H N * Real.log (1 + 1 / (N : ℝ)) -
        Real.log ((N + 1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ) ∧
    0 < D (N + 1) - D N) ∧
  (∀ (N : ℕ), 1 ≤ N →
    2 * S N ≤ H N * Real.log (N : ℝ))

end MathlibPlus.Open.Analysis.HarmonicLogDivisor

namespace MathlibPlus.Analysis.HarmonicLogDivisor

/-- The exact formalized claim is proved from the displayed finite-sum
identities and the logarithmic lower bounds above. -/
theorem harmonicLogDivisorPositivity_proved :
    MathlibPlus.Open.Analysis.HarmonicLogDivisor.harmonicLogDivisorPositivity := by
  refine ⟨D_one, ?_, ?_⟩
  · intro N hN
    exact ⟨D_succ_sub N hN, D_succ_sub_pos N hN⟩
  · exact final_bound

end MathlibPlus.Analysis.HarmonicLogDivisor
