import Mathlib

/-!
# Finite Cayley-divisor Laurent moments

Exact finite-divisor definitions and the unit-circle sum-of-squares identity from
legacy extraction packet `C-0008`. This module deliberately makes no assertion about
an infinite or regularized divisor, and it does not claim a uniform finite witness
order for off-circle points.
-/

open scoped ComplexConjugate

namespace MathlibPlus.CayleyDivisor

noncomputable section

/-- Finitely supported coefficients of a complex Laurent polynomial. -/
abbrev LaurentCoeff := ℤ →₀ ℂ

/-- Reciprocal conjugation on a complex divisor coordinate. -/
def inversionConj (w : ℂ) : ℂ := 1 / conj w

/-- A finite indexed divisor is nonzero and closed under reciprocal conjugation,
with multiplicities represented by its indices. -/
def InversionConjStable {m : ℕ} (W : Fin m → ℂ) : Prop :=
  (∀ r, W r ≠ 0) ∧ ∀ r, ∃ s, W s = inversionConj (W r)

/-- The Laurent moment of a finite indexed complex divisor. -/
def laurentMoment {m : ℕ} (W : Fin m → ℂ) (n : ℤ) : ℂ :=
  ∑ r, W r ^ n

/-- Evaluation of a finitely supported Laurent polynomial. -/
def laurentEval (p : LaurentCoeff) (w : ℂ) : ℂ :=
  p.sum fun n coefficient => coefficient * w ^ n

/-- The coefficient form of the Laurent involution
`p⁎(u) = conj (p (1 / conj u))`. -/
def laurentStar (p : LaurentCoeff) : LaurentCoeff :=
  p.sum fun n coefficient => Finsupp.single (-n) (conj coefficient)

/-- The finite-divisor Laurent moment functional. -/
def momentFunctional {m : ℕ} (W : Fin m → ℂ) (p : LaurentCoeff) : ℂ :=
  p.sum fun n coefficient => coefficient * laurentMoment W n

/-- The finite Toeplitz moment matrix through order `N`. -/
def toeplitzMomentMatrix {m : ℕ} (W : Fin m → ℂ) (N : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  fun j k => laurentMoment W ((j : ℤ) - (k : ℤ))

private lemma zpow_sub_eq_mul_conj_pow (w : ℂ) (hw : ‖w‖ = 1) (j k : ℕ) :
    w ^ ((j : ℤ) - (k : ℤ)) = w ^ j * conj (w ^ k) := by
  have hw0 : w ≠ 0 := by
    intro h
    subst w
    norm_num at hw
  rw [zpow_sub₀ hw0, zpow_natCast, zpow_natCast, div_eq_mul_inv,
    Complex.inv_def]
  have hnormSq : Complex.normSq (w ^ k) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_pow, hw]
    norm_num
  rw [hnormSq]
  simp

/-- A finite unit-circle divisor has a positive-semidefinite Laurent moment form,
expressed as an exact sum of squared moduli. -/
theorem circleMoment_sumOfSquares {m N : ℕ} (W : Fin m → ℂ)
    (hW : ∀ r, ‖W r‖ = 1) (c : Fin (N + 1) → ℂ) :
    (∑ j, ∑ k, c j * conj (c k) *
        laurentMoment W ((j : ℤ) - (k : ℤ))) =
      ∑ r, ((‖∑ j, c j * W r ^ (j : ℕ)‖ ^ 2 : ℝ) : ℂ) := by
  classical
  calc
    (∑ j, ∑ k, c j * conj (c k) *
        laurentMoment W ((j : ℤ) - (k : ℤ))) =
        ∑ j, ∑ k, ∑ r,
          c j * conj (c k) *
            (W r ^ (j : ℕ) * conj (W r ^ (k : ℕ))) := by
            simp_rw [laurentMoment, zpow_sub_eq_mul_conj_pow _ (hW _)]
            simp only [Finset.mul_sum]
    _ = ∑ j, ∑ r, ∑ k,
          c j * conj (c k) *
            (W r ^ (j : ℕ) * conj (W r ^ (k : ℕ))) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_comm]
    _ = ∑ r, ∑ j, ∑ k,
          c j * conj (c k) *
            (W r ^ (j : ℕ) * conj (W r ^ (k : ℕ))) := by
            rw [Finset.sum_comm]
    _ = ∑ r, (∑ j, c j * W r ^ (j : ℕ)) *
          conj (∑ k, c k * W r ^ (k : ℕ)) := by
            apply Finset.sum_congr rfl
            intro r _
            simp only [map_sum, map_mul]
            simp_rw [Finset.sum_mul, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro k _
            ring
    _ = ∑ r, ((‖∑ j, c j * W r ^ (j : ℕ)‖ ^ 2 : ℝ) : ℂ) := by
            apply Finset.sum_congr rfl
            intro r _
            rw [Complex.sq_norm, Complex.mul_conj]

/-- The real part of the unit-circle Laurent moment form is nonnegative. -/
theorem circleMoment_nonnegative {m N : ℕ} (W : Fin m → ℂ)
    (hW : ∀ r, ‖W r‖ = 1) (c : Fin (N + 1) → ℂ) :
    0 ≤ (∑ j, ∑ k, c j * conj (c k) *
      laurentMoment W ((j : ℤ) - (k : ℤ))).re := by
  rw [circleMoment_sumOfSquares W hW c]
  change 0 ≤ Complex.reCLM (∑ r, ((‖∑ j, c j * W r ^ (j : ℕ)‖ ^ 2 : ℝ) : ℂ))
  rw [map_sum]
  apply Finset.sum_nonneg
  intro r _
  exact sq_nonneg ‖∑ j, c j * W r ^ (j : ℕ)‖

end

end MathlibPlus.CayleyDivisor
