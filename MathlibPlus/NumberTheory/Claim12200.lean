import Mathlib.Data.Finset.SymmDiff
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace MathlibPlus.NumberTheory.Claim12200

private lemma log_nonneg_of_prime {p : ℕ} (hp : Nat.Prime p) :
    0 ≤ Real.log p := by
  have hp1 : (1 : ℝ) ≤ p := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.Prime.ne_zero hp))
  exact Real.log_nonneg hp1

private lemma feature_diff_sq {A B : Finset ℕ}
    (hA : ∀ p ∈ A, Nat.Prime p) (hB : ∀ p ∈ B, Nat.Prime p) (p : ℕ) :
    ((if p ∈ A then Real.sqrt (Real.log p) else 0) -
        (if p ∈ B then Real.sqrt (Real.log p) else 0)) ^ 2 =
      if p ∈ symmDiff A B then Real.log p else 0 := by
  classical
  by_cases hpA : p ∈ A <;> by_cases hpB : p ∈ B
  · simp [hpA, hpB, Finset.mem_symmDiff]
  · have hp : Nat.Prime p := hA p hpA
    simp only [if_pos hpA, if_neg hpB, sub_zero]
    rw [Real.sq_sqrt (log_nonneg_of_prime hp)]
    simp [Finset.mem_symmDiff, hpA, hpB]
  · have hp : Nat.Prime p := hB p hpB
    simp only [if_neg hpA, if_pos hpB, zero_sub]
    have hsq := Real.sq_sqrt (log_nonneg_of_prime hp)
    calc
      (-Real.sqrt (Real.log p)) ^ 2 = (Real.sqrt (Real.log p)) ^ 2 := by ring
      _ = Real.log p := hsq
      _ = if p ∈ symmDiff A B then Real.log p else 0 := by
        simp [Finset.mem_symmDiff, hpA, hpB]
  · simp [hpA, hpB, Finset.mem_symmDiff]

/--
Claim 12200: for finite prime configurations, the coordinate-modulus feature
map has squared distance equal to the logarithmic symmetric-difference sum.
The incidence kernel `K`, cut distance `d`, and finite-support squared norm are
kept as local definitions so this statement introduces no separate public
vocabulary before fidelity review.
-/
theorem primeCutDistance_eq_featureSqNorm {A B : Finset ℕ}
    (hA : ∀ p ∈ A, Nat.Prime p) (hB : ∀ p ∈ B, Nat.Prime p) :
    let Φ : Finset ℕ → ℕ → ℝ :=
      fun S p => if p ∈ S then Real.sqrt (Real.log p) else 0
    let K : Finset ℕ → Finset ℕ → ℝ :=
      fun S T => (S ∩ T).sum (fun p => Real.log p)
    let d : Finset ℕ → Finset ℕ → ℝ :=
      fun S T => (symmDiff S T).sum (fun p => Real.log p)
    let normSq : Finset ℕ → Finset ℕ → ℝ :=
      fun S T => (S ∪ T).sum (fun p => (Φ S p - Φ T p) ^ 2)
    d A B = normSq A B := by
  dsimp
  have hsubset : symmDiff A B ⊆ A ∪ B := Finset.symmDiff_subset_union
  have hzero : ∀ p ∈ A ∪ B, p ∉ symmDiff A B →
      (if p ∈ symmDiff A B then Real.log p else 0) = 0 := by
    intro p hpUnion hpDiff
    simp [hpDiff]
  calc
    (symmDiff A B).sum (fun p => Real.log p) =
        (A ∪ B).sum (fun p => if p ∈ symmDiff A B then Real.log p else 0) := by
      simpa using (Finset.sum_subset hsubset hzero)
    _ = (A ∪ B).sum (fun p =>
          ((if p ∈ A then Real.sqrt (Real.log p) else 0) -
            (if p ∈ B then Real.sqrt (Real.log p) else 0)) ^ 2) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [feature_diff_sq hA hB p]

end MathlibPlus.NumberTheory.Claim12200
