import Mathlib

namespace MathlibPlus.Algebra

/-- Claim 16947: stable finiteness of all matrix rings implies direct finiteness
of the base ring.  The two finiteness predicates are expanded in the statement
so that the matrix size and the quantifiers are explicit. -/
theorem stableFiniteness_implies_directFiniteness_claim16947
    {R : Type*} [Ring R]
    (hR : ∀ n : ℕ,
      ∀ ⦃A B : Matrix (Fin n) (Fin n) R⦄,
        A * B = 1 → B * A = 1) :
    ∀ ⦃a b : R⦄, a * b = 1 → b * a = 1 := by
  intro a b hab
  let A : Matrix (Fin 1) (Fin 1) R := Matrix.diagonal (fun _ => a)
  let B : Matrix (Fin 1) (Fin 1) R := Matrix.diagonal (fun _ => b)
  have hAB : A * B = 1 := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    · simpa [A, B, Matrix.mul_apply, Fin.sum_univ_one] using hab
  have hBA : B * A = 1 := hR 1 hAB
  have hentry := congrArg (fun M : Matrix (Fin 1) (Fin 1) R => M 0 0) hBA
  simpa [A, B, Matrix.mul_apply, Fin.sum_univ_one] using hentry

end MathlibPlus.Algebra
