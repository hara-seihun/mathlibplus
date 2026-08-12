import MathlibPlus.Basic

namespace MathlibPlus.Analysis.Claim11843

/--
Claim 11843.  For the explicit polynomial
`B(z) = (1+z)^10 (1+13z) (1+14z)^2`, the factorial-scaled coefficient
sequence has positive centered Toeplitz determinants at orders 2, 3, and 4,
but a negative centered determinant at order 5.  The coefficient certificate
is included so the matrices are tied to the source polynomial rather than
being an unrelated replay of its reported integer values.
-/
theorem firstFailureCenteredDeterminants :
    let B : Polynomial ℤ :=
      (1 + Polynomial.X) ^ 10 * (1 + 13 * Polynomial.X) *
        (1 + 14 * Polynomial.X) ^ 2
    let c : Fin 9 → ℤ :=
      ![1, 51, 2030, 60678, 1339440, 22886640, 312409440,
        3452047200, 30831131520]
    (∀ k : Fin 9, c k = (Nat.factorial k.1 : ℤ) * B.coeff k.1) ∧
      0 < Matrix.det (!![c 4, c 5; c 3, c 4] : Matrix (Fin 2) (Fin 2) ℤ) ∧
      0 < Matrix.det (!![c 4, c 5, c 6; c 3, c 4, c 5; c 2, c 3, c 4] :
        Matrix (Fin 3) (Fin 3) ℤ) ∧
      0 < Matrix.det (!![c 4, c 5, c 6, c 7;
        c 3, c 4, c 5, c 6;
        c 2, c 3, c 4, c 5;
        c 1, c 2, c 3, c 4] : Matrix (Fin 4) (Fin 4) ℤ) ∧
      Matrix.det (!![c 4, c 5, c 6, c 7, c 8;
        c 3, c 4, c 5, c 6, c 7;
        c 2, c 3, c 4, c 5, c 6;
        c 1, c 2, c 3, c 4, c 5;
        c 0, c 1, c 2, c 3, c 4] : Matrix (Fin 5) (Fin 5) ℤ) < 0 := by
  dsimp
  have hB :
      ((1 : Polynomial ℤ) + Polynomial.X) ^ 10 *
          (1 + 13 * Polynomial.X) * (1 + 14 * Polynomial.X) ^ 2 =
      1 + 51 * Polynomial.X + 1015 * Polynomial.X ^ 2 +
        10113 * Polynomial.X ^ 3 + 55810 * Polynomial.X ^ 4 +
        190722 * Polynomial.X ^ 5 + 433902 * Polynomial.X ^ 6 +
        684930 * Polynomial.X ^ 7 + 764661 * Polynomial.X ^ 8 +
        604135 * Polynomial.X ^ 9 + 331371 * Polynomial.X ^ 10 +
        120301 * Polynomial.X ^ 11 + 26040 * Polynomial.X ^ 12 +
        2548 * Polynomial.X ^ 13 := by
    ring_nf
  rw [hB]
  constructor
  · intro k
    fin_cases k <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_one, Polynomial.coeff_X, Nat.factorial]
  · native_decide

end MathlibPlus.Analysis.Claim11843
