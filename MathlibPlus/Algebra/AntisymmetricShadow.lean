import Mathlib

namespace MathlibPlus.Algebra.AntisymmetricShadow

/-- Claim 10619: the displayed antisymmetric cubic factors over the reals. -/
theorem polynomialFactorization (a q : ℝ) :
    1 + a * q - a * q ^ 2 - q ^ 3 =
      (1 - q) * (q ^ 2 + (a + 1) * q + 1) := by
  ring

/--
Claim 10619: for every real `a > 1`, the quadratic factor has two distinct
negative reciprocal real roots, neither on the real unit circle.  The real
statement includes the rational case from the source.
-/
theorem quadraticRoots {a : ℝ} (ha : 1 < a) :
    0 < (a + 1) ^ 2 - 4 ∧
      ∃ rminus rplus : ℝ,
        rminus ≠ rplus ∧
        rminus ^ 2 + (a + 1) * rminus + 1 = 0 ∧
        rplus ^ 2 + (a + 1) * rplus + 1 = 0 ∧
        rminus < 0 ∧ rplus < 0 ∧
        rminus * rplus = 1 ∧
        |rminus| ≠ 1 ∧ |rplus| ≠ 1 := by
  have hfactor : (a + 1) ^ 2 - 4 = (a - 1) * (a + 3) := by
    ring
  have hdisc : 0 < (a + 1) ^ 2 - 4 := by
    rw [hfactor]
    positivity
  let d : ℝ := Real.sqrt ((a + 1) ^ 2 - 4)
  have hd_sq : d ^ 2 = (a + 1) ^ 2 - 4 := by
    dsimp [d]
    exact Real.sq_sqrt (le_of_lt hdisc)
  have hd_pos : 0 < d := by
    dsimp [d]
    exact Real.sqrt_pos.2 hdisc
  have hbase_pos : 0 < a + 1 := by
    linarith
  have hd_lt : d < a + 1 := by
    nlinarith
  let rminus : ℝ := (-(a + 1) - d) / 2
  let rplus : ℝ := (-(a + 1) + d) / 2
  have hminus_neg : rminus < 0 := by
    dsimp [rminus]
    linarith
  have hplus_neg : rplus < 0 := by
    dsimp [rplus]
    linarith
  have hminus_root : rminus ^ 2 + (a + 1) * rminus + 1 = 0 := by
    dsimp [rminus]
    nlinarith
  have hplus_root : rplus ^ 2 + (a + 1) * rplus + 1 = 0 := by
    dsimp [rplus]
    nlinarith
  have hprod : rminus * rplus = 1 := by
    dsimp [rminus, rplus]
    nlinarith
  have hdistinct : rminus ≠ rplus := by
    dsimp [rminus, rplus]
    linarith
  have hminus_not_neg_one : rminus ≠ -1 := by
    intro h
    rw [h] at hminus_root
    nlinarith
  have hplus_not_neg_one : rplus ≠ -1 := by
    intro h
    rw [h] at hplus_root
    nlinarith
  have hminus_unit : |rminus| ≠ 1 := by
    intro h
    rw [abs_of_neg hminus_neg] at h
    apply hminus_not_neg_one
    linarith
  have hplus_unit : |rplus| ≠ 1 := by
    intro h
    rw [abs_of_neg hplus_neg] at h
    apply hplus_not_neg_one
    linarith
  exact ⟨hdisc, rminus, rplus, hdistinct, hminus_root, hplus_root,
    hminus_neg, hplus_neg, hprod, hminus_unit, hplus_unit⟩

end MathlibPlus.Algebra.AntisymmetricShadow
