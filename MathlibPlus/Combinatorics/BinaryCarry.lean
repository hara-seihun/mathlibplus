import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace MathlibPlus.Combinatorics.BinaryCarry

/-! Formalization of admitted claim 47358.

The source indexes a binary prefix from `1` through `k`.  We represent its
entries by `d : Fin k → ℕ` together with the explicit binary bound.  The
rational expression is kept over `ℚ`, so “the carry is an integer” is stated
without truncating rational arithmetic.  The source does not give an
independent predicate for “feasible”; here it is recorded literally as the
announced integer interval.
-/

def nextCarry (k : ℕ) (r : ℤ) (digit : Bool) : ℤ :=
  if digit then 2 * r - 15 * (k + 1) else 2 * r

def childFeasible (k : ℕ) (r : ℤ) (digit : Bool) : Prop :=
  0 ≤ nextCarry k r digit ∧ nextCarry k r digit ≤ 15 * (k + 3)

@[simp] theorem nextCarry_false (k : ℕ) (r : ℤ) :
    nextCarry k r false = 2 * r := by
  rfl

@[simp] theorem nextCarry_true (k : ℕ) (r : ℤ) :
    nextCarry k r true = 2 * r - 15 * (k + 1) := by
  rfl

theorem childFeasible_iff_interval (k : ℕ) (r : ℤ) (digit : Bool) :
    childFeasible k r digit ↔
      0 ≤ nextCarry k r digit ∧ nextCarry k r digit ≤ 15 * (k + 3) := by
  rfl

private lemma pow_clear (k : ℕ) (j : Fin k) (x : ℚ) :
    (2 : ℚ)^k * (x / (2 : ℚ)^(j.val + 1)) =
      x * (2 : ℚ)^(k - (j.val + 1)) := by
  have hj : j.val + 1 ≤ k := Nat.succ_le_of_lt j.isLt
  rw [pow_sub₀ (2 : ℚ) (by norm_num) hj]
  field_simp

/-- The carry expression in claim 47358 is integral for every binary prefix. -/
theorem prefixCarry_is_integer (k : ℕ) (d : Fin k → ℕ)
    (_hd : ∀ j, d j ≤ 1) :
    ∃ r : ℤ,
      (r : ℚ) =
        15 * (2 : ℚ)^k *
          (14 / 15 - ∑ j : Fin k,
            ((j.val + 1 : ℚ) * (d j : ℚ) / (2 : ℚ)^(j.val + 1))) := by
  let r : ℤ :=
    14 * (2 : ℤ)^k -
      15 * ∑ j : Fin k,
        (j.val + 1 : ℤ) * (d j : ℤ) * (2 : ℤ)^(k - (j.val + 1))
  refine ⟨r, ?_⟩
  dsimp [r]
  norm_num [Int.cast_sub, Int.cast_mul, Int.cast_pow]
  rw [mul_sub, Finset.mul_sum]
  have hsum :
      (∑ i : Fin k, 15 * ((i.val + 1 : ℚ) * (d i : ℚ) *
          (2 : ℚ)^(k - (i.val + 1)))) =
        15 * (2 : ℚ)^k * ∑ j : Fin k,
          ((j.val + 1 : ℚ) * (d j : ℚ) / (2 : ℚ)^(j.val + 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← pow_clear k j ((j.val + 1 : ℚ) * (d j : ℚ))]
    ring
  rw [hsum]
  ring

end MathlibPlus.Combinatorics.BinaryCarry
