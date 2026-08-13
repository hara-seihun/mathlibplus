import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim25562

/-!
Scoped formal consequence of admitted claim 25562.  The source identifies a
module dimension with the index of a dihedral subgroup and then gives the
factorial quotient.  This declaration records only the exact arithmetic
consequence; the source-specific symmetric-group, dihedral-subgroup, and
induced-module bridge is deliberately left for a separate faithful
formalization.
-/

/-- For every positive `n`, the factorial quotient appearing in claim 25562
has the displayed simplified form. -/
theorem factorialIndexArithmetic_claim25562 (n : ℕ) (hn : 0 < n) :
    Nat.factorial n / (2 * n) = Nat.factorial (n - 1) / 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [Nat.factorial_succ]
  rw [Nat.mul_comm 2 (m + 1)]
  rw [Nat.mul_div_mul_left]
  · rfl
  · exact Nat.zero_lt_succ m

end MathlibPlus.Algebra.Claim25562
