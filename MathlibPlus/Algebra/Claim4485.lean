import MathlibPlus.Basic

open scoped BigOperators

namespace MathlibPlus.Algebra.Claim4485

/-!
The packet's `h_k(a,b)` is formalized as the two-variable complete homogeneous
polynomial `Σ_{i=0}^k a^i b^(k-i)`. The subsequent symbols `τ_x` and `u_x(p)`
are not defined in the admitted claim text, so the Hecke specialization is
left as an explicit fidelity-review boundary.
-/

/-- Two-variable complete homogeneous polynomial. -/
def completeHomogeneous {R : Type*} [CommRing R] (k : ℕ) (a b : R) : R :=
  ∑ i ∈ Finset.range (k + 1), a ^ i * b ^ (k - i)

private lemma completeHomogeneous_succ {R : Type*} [CommRing R]
    (k : ℕ) (a b : R) :
    completeHomogeneous (k + 1) a b =
      a * completeHomogeneous k a b + b ^ (k + 1) := by
  unfold completeHomogeneous
  rw [show k + 1 + 1 = (k + 1) + 1 by omega, Finset.sum_range_succ']
  rw [Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hsub : k + 1 - (i + 1) = k - i := Nat.succ_sub_succ k i
    rw [hsub, pow_succ]
    ring
  · simp

/-- Claim 4485: if `a*b=1`, the complete homogeneous sequence obeys the
second-order Hecke recurrence. -/
theorem completeHomogeneous_two_step (a b : ℚ) (hab : a * b = 1) (k : ℕ) :
    completeHomogeneous (k + 2) a b =
      (a + b) * completeHomogeneous (k + 1) a b -
        completeHomogeneous k a b := by
  rw [completeHomogeneous_succ (k + 1) a b,
    completeHomogeneous_succ k a b]
  rw [show k + 1 + 1 = k + 2 by omega]
  rw [pow_add]
  ring_nf
  linear_combination -hab * completeHomogeneous k a b

end MathlibPlus.Algebra.Claim4485
