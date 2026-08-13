import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim57342

open Polynomial

/-- The Lehmer polynomial after the substitution `x ↦ x^K`. -/
noncomputable def lehmerSubstitute (K : ℕ) : ℤ[X] :=
    (X ^ K) ^ 10 + (X ^ K) ^ 9 - (X ^ K) ^ 7 - (X ^ K) ^ 6
      - (X ^ K) ^ 5 - (X ^ K) ^ 4 - (X ^ K) ^ 3 + (X ^ K) + 1

/-- The central companion obtained by changing the coefficient of `x^(5K)`. -/
noncomputable def companion (K : ℕ) : ℤ[X] := lehmerSubstitute K + X ^ (5 * K)

/-- Exact cyclotomic companion factorization. -/
theorem companion_factorization (K : ℕ) :
    companion K = (X ^ K - 1) ^ 2 * (X ^ K + 1) ^ 2
      * (X ^ (2 * K) + X ^ K + 1) ^ 2
      * (X ^ (2 * K) - X ^ K + 1) := by
  dsimp [companion, lehmerSubstitute]
  rw [show X ^ (5 * K) = (X ^ K : ℤ[X]) ^ 5 by
    rw [show 5 * K = K * 5 by omega, pow_mul]]
  rw [show X ^ (2 * K) = (X ^ K : ℤ[X]) ^ 2 by
    rw [show 2 * K = K * 2 by omega, pow_mul]]
  ring

end MathlibPlus.Algebra.Claim57342
