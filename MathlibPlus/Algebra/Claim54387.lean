import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace MathlibPlus.Algebra.Claim54387

/-- The root-to-root difference telescopes along any finite sequence of roots. -/
theorem root_path_telescope {V R : Type*} [AddCommGroup R]
    (P : V → R) (v : ℕ → V) (m : ℕ) :
    P (v 0) - P (v m) =
      ∑ i ∈ Finset.range m, (P (v i) - P (v (i + 1))) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      calc
        P (v 0) - P (v (Nat.succ m)) =
            (P (v 0) - P (v m)) +
              (P (v m) - P (v (Nat.succ m))) := by abel
        _ = ∑ i ∈ Finset.range m, (P (v i) - P (v (i + 1))) +
              (P (v m) - P (v (m + 1))) := by
            rw [ih]

/-- The product difference expands into the simultaneous-reroot telescope. -/
theorem product_telescope {R : Type*} [CommRing R]
    (f g : ℕ → R) (q : ℕ) :
    (∏ i ∈ Finset.range q, f i) - (∏ i ∈ Finset.range q, g i) =
      ∑ i ∈ Finset.range q,
        (∏ j ∈ Finset.range i, g j) * (f i - g i) *
          (∏ j ∈ Finset.Ico (i + 1) q, f j) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ,
        Finset.sum_range_succ]
      have hmain :
          (∑ i ∈ Finset.range q,
            (∏ j ∈ Finset.range i, g j) * (f i - g i) *
              (∏ j ∈ Finset.Ico (i + 1) (q + 1), f j)) =
            (∑ i ∈ Finset.range q,
              (∏ j ∈ Finset.range i, g j) * (f i - g i) *
                (∏ j ∈ Finset.Ico (i + 1) q, f j)) * f q := by
        calc
          (∑ i ∈ Finset.range q,
            (∏ j ∈ Finset.range i, g j) * (f i - g i) *
              (∏ j ∈ Finset.Ico (i + 1) (q + 1), f j)) =
              ∑ i ∈ Finset.range q,
                ((∏ j ∈ Finset.range i, g j) * (f i - g i) *
                  (∏ j ∈ Finset.Ico (i + 1) q, f j)) * f q := by
            apply Finset.sum_congr rfl
            intro i hi
            have hiq : i < q := Finset.mem_range.mp hi
            have hle : i + 1 ≤ q := Nat.succ_le_iff.mp (Nat.succ_le_of_lt hiq)
            rw [Finset.prod_Ico_succ_top hle]
            ring
          _ = (∑ i ∈ Finset.range q,
              (∏ j ∈ Finset.range i, g j) * (f i - g i) *
                (∏ j ∈ Finset.Ico (i + 1) q, f j)) * f q := by
            rw [Finset.sum_mul]
      rw [hmain]
      simp only [Finset.Ico_self, Finset.prod_empty, mul_one]
      calc
        (∏ x ∈ Finset.range q, f x) * f q -
              (∏ x ∈ Finset.range q, g x) * g q =
            ((∏ x ∈ Finset.range q, f x) -
              (∏ x ∈ Finset.range q, g x)) * f q +
              (∏ x ∈ Finset.range q, g x) * (f q - g q) := by ring
        _ = (∑ i ∈ Finset.range q,
              (∏ j ∈ Finset.range i, g j) * (f i - g i) *
                (∏ j ∈ Finset.Ico (i + 1) q, f j)) * f q +
              (∏ x ∈ Finset.range q, g x) * (f q - g q) := by
            rw [ih]

end MathlibPlus.Algebra.Claim54387
