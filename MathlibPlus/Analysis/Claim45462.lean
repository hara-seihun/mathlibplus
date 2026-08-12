import Mathlib

namespace MathlibPlus.Analysis.Claim45462

/-- Claim 45462: the displayed exact expected potential drop for an address-bit
query.  `N` is the positive number of components and `d` is the real parameter
under the square roots; the casts and the domain `1 ≤ d` are explicit. -/
theorem addressBitPotentialDrop
    (N : ℕ) (d : ℝ) (hN : 0 < N) (hd : 1 ≤ d) :
    d - ((((N : ℝ) - 1) * Real.sqrt d + Real.sqrt (d - 1)) / (N : ℝ)) ^ 2 =
      (1 + 2 * ((N : ℝ) - 1) *
        (d - Real.sqrt (d * (d - 1)))) / (N : ℝ) ^ 2 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hd0 : 0 ≤ d := by linarith
  have hm0 : 0 ≤ d - 1 := by linarith
  have hsd : (Real.sqrt d) ^ 2 = d := Real.sq_sqrt hd0
  have hsm : (Real.sqrt (d - 1)) ^ 2 = d - 1 := Real.sq_sqrt hm0
  have hmul : Real.sqrt d * Real.sqrt (d - 1) = Real.sqrt (d * (d - 1)) := by
    rw [← Real.sqrt_mul hd0]
  field_simp [hn]
  nlinarith [hsd, hsm, hmul]

/-- The strict square-root gap used in the final inequalities of claim 45462. -/
theorem squareRootGap
    (d : ℝ) (hd : 1 < d) :
    0 < d - Real.sqrt (d * (d - 1)) ∧
      d - Real.sqrt (d * (d - 1)) < 1 := by
  have hd0 : 0 ≤ d := by linarith
  have hprod0 : 0 ≤ d * (d - 1) := by positivity
  have hs0 : 0 ≤ Real.sqrt (d * (d - 1)) := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt (d * (d - 1))) ^ 2 = d * (d - 1) :=
    Real.sq_sqrt hprod0
  constructor <;> nlinarith

/-- Claim 45462: under the source's strict square-root-gap condition and
`N > 1`, the exact drop is below `(2N-1)/N²`, which is below `2/N`. -/
theorem addressBitPotentialDropBounds
    (N : ℕ) (d : ℝ) (hN : 0 < N) (hN2 : 1 < N) (hd : 1 ≤ d)
    (hgap0 : 0 < d - Real.sqrt (d * (d - 1)))
    (hgap1 : d - Real.sqrt (d * (d - 1)) < 1) :
    d - ((((N : ℝ) - 1) * Real.sqrt d + Real.sqrt (d - 1)) / (N : ℝ)) ^ 2 <
        (2 * (N : ℝ) - 1) / (N : ℝ) ^ 2 ∧
      (2 * (N : ℝ) - 1) / (N : ℝ) ^ 2 < 2 / (N : ℝ) := by
  have hnpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hnge : 1 ≤ (N : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hN))
  have hcoefpos : 0 < 2 * ((N : ℝ) - 1) := by
    have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN2
    linarith
  have hden : 0 < (N : ℝ) ^ 2 := sq_pos_of_pos hnpos
  have hprod :
      2 * ((N : ℝ) - 1) * (d - Real.sqrt (d * (d - 1))) <
        2 * ((N : ℝ) - 1) := by
    simpa using mul_lt_mul_of_pos_left hgap1 hcoefpos
  have hnum :
      1 + 2 * ((N : ℝ) - 1) * (d - Real.sqrt (d * (d - 1))) <
        1 + 2 * ((N : ℝ) - 1) := by
    linarith
  have hfirst :
      (1 + 2 * ((N : ℝ) - 1) * (d - Real.sqrt (d * (d - 1)))) / (N : ℝ) ^ 2 <
        (2 * (N : ℝ) - 1) / (N : ℝ) ^ 2 := by
    calc
      _ < (1 + 2 * ((N : ℝ) - 1)) / (N : ℝ) ^ 2 :=
        (div_lt_div_iff_of_pos_right hden).2 hnum
      _ = (2 * (N : ℝ) - 1) / (N : ℝ) ^ 2 := by ring
  have hsecond : (2 * (N : ℝ) - 1) / (N : ℝ) ^ 2 < 2 / (N : ℝ) := by
    apply (div_lt_iff₀ hden).2
    field_simp [ne_of_gt hnpos]
    nlinarith
  exact ⟨addressBitPotentialDrop N d hN hd ▸ hfirst, hsecond⟩

end MathlibPlus.Analysis.Claim45462
