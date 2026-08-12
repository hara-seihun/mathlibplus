import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators

namespace MathlibPlus.Analysis

/--
Claim 51031 (R-3626.2): the restricted endpoint contraction obeys
Cauchy--Schwarz under a normalized finite law.  A finite event is represented
by a `Finset`; the two displayed restricted square energies are retained
without adding a shell-specific interface.
-/
theorem restrictedOneHoleCauchySchwarz {α : Type*} [Fintype α] [DecidableEq α]
    (ν F G : α → ℝ) (E : Finset α)
    (hν : ∀ x, 0 ≤ ν x) (_hprob : ∑ x, ν x = 1) :
    abs ((∑ x ∈ E, ν x * F x * G x)) ≤
      √((∑ x ∈ E, ν x * F x ^ 2)) * √((∑ x ∈ E, ν x * G x ^ 2)) := by
  have hs :
      (∑ x ∈ E, ν x * F x * G x) ^ 2 ≤
        (∑ x ∈ E, ν x * F x ^ 2) * ∑ x ∈ E, ν x * G x ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul E
    · intro x hx
      exact mul_nonneg (hν x) (sq_nonneg _)
    · intro x hx
      exact mul_nonneg (hν x) (sq_nonneg _)
    · intro x hx
      ring_nf
      exact le_rfl
  calc
    abs ((∑ x ∈ E, ν x * F x * G x)) ≤
        √(((∑ x ∈ E, ν x * F x ^ 2) * (∑ x ∈ E, ν x * G x ^ 2))) :=
      Real.abs_le_sqrt hs
    _ = √((∑ x ∈ E, ν x * F x ^ 2)) * √((∑ x ∈ E, ν x * G x ^ 2)) := by
      rw [Real.sqrt_mul (Finset.sum_nonneg fun x hx =>
        mul_nonneg (hν x) (sq_nonneg _))]

end MathlibPlus.Analysis
