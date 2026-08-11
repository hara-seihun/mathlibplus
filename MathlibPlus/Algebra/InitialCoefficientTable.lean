import Mathlib

namespace MathlibPlus.Algebra.InitialCoefficientTable

/--
Claim 14827.  The source defines `c_k = k! * b_k`; with that factorial
scaling, the displayed first seven coefficients are exactly the following.
-/
theorem initialCoefficientTable :
    let B : Polynomial ℤ := (1 + 162 * Polynomial.X)^2 *
      (1 + Polynomial.X)^11
    let b := fun n : Fin 7 => B.coeff n
    let c := fun n : Fin 7 => (Nat.factorial (n : ℕ) : ℤ) * b n
    (b 0, b 1, b 2, b 3, b 4, b 5, b 6) =
        (1, 335, 29863, 306669, 1497210, 4437642, 8810670) ∧
      (c 0, c 1, c 2, c 3, c 4, c 5, c 6) =
        (1, 335, 59726, 1840014, 35933040, 532517040, 6343682400) := by
  dsimp
  have h : ((1 : Polynomial ℤ) + 162 * Polynomial.X)^2 *
        (1 + Polynomial.X)^11 =
      1 + 335 * Polynomial.X + 29863 * Polynomial.X^2 +
        306669 * Polynomial.X^3 + 1497210 * Polynomial.X^4 +
        4437642 * Polynomial.X^5 + 8810670 * Polynomial.X^6 +
        12274746 * Polynomial.X^7 + 12231813 * Polynomial.X^8 +
        8714035 * Polynomial.X^9 + 4348091 * Polynomial.X^10 +
        1446985 * Polynomial.X^11 + 289008 * Polynomial.X^12 +
        26244 * Polynomial.X^13 := by
    ring_nf
  rw [h]
  simp [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X]
  norm_num [Nat.factorial]

end MathlibPlus.Algebra.InitialCoefficientTable
