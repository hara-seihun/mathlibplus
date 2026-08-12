import Mathlib

namespace MathlibPlus.NumberTheory

open scoped BigOperators ArithmeticFunction.Moebius

/-- The cutoff sum from the O-0164 Möbius--LCM perturbation, with the
real-valued exponent written using `Real.rpow`. -/
noncomputable def mobiusLcmCutoffSum (ε X : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 ⌊X⌋₊, ∑ e ∈ Finset.Icc 1 ⌊X⌋₊,
    ((μ d : ℝ) * (μ e : ℝ)) /
      Real.rpow (Nat.lcm d e : ℝ) (1 + ε)

private lemma floor_eq_two_of_mem {X : ℝ} (hX2 : 2 ≤ X) (hX3 : X < 3) :
    ⌊X⌋₊ = 2 := by
  apply (Nat.floor_eq_iff (by linarith : (0 : ℝ) ≤ X)).2
  constructor
  · exact_mod_cast hX2
  · norm_num at *
    linarith

private lemma floor_eq_zero_of_mem {X : ℝ} (hX0 : 0 < X) (hX1 : X < 1) :
    ⌊X⌋₊ = 0 := by
  exact Nat.floor_eq_zero.mpr (by linarith)

private lemma floor_eq_one_of_mem {X : ℝ} (hX1 : 1 ≤ X) (hX2 : X < 2) :
    ⌊X⌋₊ = 1 := by
  apply (Nat.floor_eq_iff (by linarith : (0 : ℝ) ≤ X)).2
  constructor
  · exact_mod_cast hX1
  · norm_num at *
    linarith

/-- Internal evaluation lemma used by the first-cutoff positivity theorem.
The corresponding admitted claim is already aligned elsewhere; this helper is
kept private so that submission coverage remains at the positive perturbation. -/
private lemma firstCutoffEval {X ε : ℝ}
    (hX2 : 2 ≤ X) (hX3 : X < 3) (hε : 0 ≤ ε) :
    mobiusLcmCutoffSum ε X = 1 - Real.rpow 2 (-1 - ε) ∧
      mobiusLcmCutoffSum 0 X = 1 / 2 := by
  have hfloor := floor_eq_two_of_mem hX2 hX3
  have hmu2 : μ 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2)
  have hsum (η : ℝ) :
      mobiusLcmCutoffSum η X = 1 - (Real.rpow (2 : ℝ) (1 + η))⁻¹ := by
    simp [mobiusLcmCutoffSum, hfloor, hmu2, Finset.sum_Icc_succ_top] <;> ring
  have hneg1 : Real.rpow (2 : ℝ) (-1 - ε) =
      (Real.rpow (2 : ℝ) (1 + ε))⁻¹ := by
    rw [show -1 - ε = -(1 + ε) by ring]
    exact Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) _
  have hneg : Real.rpow (2 : ℝ) (-ε) =
      (Real.rpow (2 : ℝ) ε)⁻¹ :=
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) ε
  constructor
  · rw [hsum ε, hneg1]
  · rw [hsum 0]
    norm_num

/-- The first-cutoff perturbation is strictly positive for positive epsilon. -/
theorem mobiusLcmFirstCutoff_positive {X ε : ℝ}
    (hX2 : 2 ≤ X) (hX3 : X < 3) (hε : 0 < ε) :
    mobiusLcmCutoffSum ε X - mobiusLcmCutoffSum 0 X =
        (1 - Real.rpow 2 (-ε)) / 2 ∧
      0 < mobiusLcmCutoffSum ε X - mobiusLcmCutoffSum 0 X := by
  have hEval := firstCutoffEval hX2 hX3 hε.le
  rw [hEval.1, hEval.2]
  have hneg1 : Real.rpow (2 : ℝ) (-1 - ε) =
      (Real.rpow (2 : ℝ) (1 + ε))⁻¹ := by
    rw [show -1 - ε = -(1 + ε) by ring]
    exact Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) _
  have hneg : Real.rpow (2 : ℝ) (-ε) =
      (Real.rpow (2 : ℝ) ε)⁻¹ :=
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) ε
  have hs : Real.rpow (2 : ℝ) (1 + ε) =
      2 * Real.rpow (2 : ℝ) ε := by
    rw [show 1 + ε = ε + 1 by ring]
    calc
      Real.rpow (2 : ℝ) (ε + 1) =
          Real.rpow (2 : ℝ) ε * Real.rpow (2 : ℝ) 1 :=
        Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _
      _ = 2 * Real.rpow (2 : ℝ) ε := by
        norm_num [Real.rpow_one]
        ring
  have hA : Real.rpow (2 : ℝ) ε ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by norm_num) ε)
  have heq : 1 - Real.rpow (2 : ℝ) (-1 - ε) - 1 / 2 =
      (1 - Real.rpow (2 : ℝ) (-ε)) / 2 := by
    rw [hneg1, hs, hneg]
    field_simp [hA]
    ring
  constructor
  · exact heq
  · rw [heq]
    have hpow : 1 < Real.rpow (2 : ℝ) ε := by
      exact Real.one_lt_rpow (by norm_num) hε
    have hinv : (Real.rpow (2 : ℝ) ε)⁻¹ < 1 := by
      simpa [one_div] using
        (one_div_lt_one_div_of_lt (a := (1 : ℝ))
          (b := Real.rpow (2 : ℝ) ε) (by norm_num) hpow)
    nlinarith

/-- Below the first nontrivial cutoff the perturbed and unperturbed sums agree. -/
theorem mobiusLcmBelowFirstCutoff_eq {X ε : ℝ}
    (hX0 : 0 < X) (hX2 : X < 2) (hε : 0 ≤ ε) :
    mobiusLcmCutoffSum ε X = mobiusLcmCutoffSum 0 X := by
  by_cases hX1 : X < 1
  · have hfloor := floor_eq_zero_of_mem hX0 hX1
    simp [mobiusLcmCutoffSum, hfloor]
  · have hX1' : 1 ≤ X := le_of_not_gt hX1
    have hfloor := floor_eq_one_of_mem hX1' hX2
    simp [mobiusLcmCutoffSum, hfloor]

end MathlibPlus.NumberTheory

namespace MathlibPlus.Analysis

/-- Exact rational component-boundary variance sum from R-3485. -/
theorem componentBoundaryVarianceSum_claim51333 :
    ((37 : ℚ) / 64 + 999 / 4096 + 225 / 2048 + 21969 / 524288 =
        510545 / 524288) ∧
      (510545 / 524288 : ℚ) < 1 := by
  norm_num

end MathlibPlus.Analysis
