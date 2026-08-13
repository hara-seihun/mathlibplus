import Mathlib

open scoped BigOperators

namespace MathlibPlus.Algebra.PullFirstClaim6592_23780

/-- Claim 6592, in exponent-vector form: the common factorwise minimum
splits each of three finite factor products into the common part and a
pointwise residual. -/
theorem commonRootedFactorGcd_residual_claim6592
    {F : Type*} [DecidableEq F] (e : Fin 3 → F →₀ ℕ) :
    ∀ (i : Fin 3) (f : F),
      e i f =
        min (min (e 0 f) (e 1 f)) (e 2 f) +
          (e i f - min (min (e 0 f) (e 1 f)) (e 2 f)) := by
  intro i f
  have hle : min (min (e 0 f) (e 1 f)) (e 2 f) ≤ e i f := by
    fin_cases i
    · exact le_trans (min_le_left _ _) (min_le_left _ _)
    · exact le_trans (min_le_left _ _) (min_le_right _ _)
    · exact min_le_right _ _
  exact (Nat.add_sub_of_le hle).symm

/-- Claim 23780, its exact complete-cell activation core: a cell is after
both birth indices and the cutoff precisely when it is after their maximum. -/
theorem maximumBirthActivationIndex_claim23780
    (N₀ N₁ A B N : ℕ) (_hcut : N₀ < N₁) :
    (N₀ ≤ N ∧ N < N₁ ∧ A ≤ N ∧ B ≤ N) ↔
      (max N₀ (max A B) ≤ N ∧ N < N₁) := by
  simp only [Nat.max_le]
  omega

/-- Claim 20828, its affine-boundary core: after the proper margins are
fixed, the displayed empty-cell expression has at most one integer parameter
value at which it vanishes. -/
theorem emptyCell_uniqueBoundary_claim20828
    (r : ℕ) (q : ℤ) (m : Finset (Fin r) → ℤ) (t₁ t₂ : ℤ)
    (h₁ : q -
        ∑ T ∈ (Finset.univ : Finset (Finset (Fin r))).filter
          (fun T => T.Nonempty ∧ T ⊂ (Finset.univ : Finset (Fin r))),
          (-1 : ℤ) ^ (T.card + 1) * m T + (-1 : ℤ) ^ r * t₁ = 0)
    (h₂ : q -
        ∑ T ∈ (Finset.univ : Finset (Finset (Fin r))).filter
          (fun T => T.Nonempty ∧ T ⊂ (Finset.univ : Finset (Fin r))),
          (-1 : ℤ) ^ (T.card + 1) * m T + (-1 : ℤ) ^ r * t₂ = 0) :
    t₁ = t₂ := by
  have hpow : (-1 : ℤ) ^ r ≠ 0 := pow_ne_zero r (by norm_num)
  have hmul : (-1 : ℤ) ^ r * t₁ = (-1 : ℤ) ^ r * t₂ := by
    linarith
  exact mul_left_cancel₀ hpow hmul

end MathlibPlus.Algebra.PullFirstClaim6592_23780
