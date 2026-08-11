import Mathlib

namespace MathlibPlus.Algebra

/-- The order-four factorial Toeplitz determinant of
`B_A(z) = (1 + A z)^2 (1 + z)^11`, with the coefficient expansion made
explicit (admitted claim 14831). -/
theorem orderFourDeterminantFamily_14831 (A : ℤ) :
    let b : ℕ → ℤ := fun k =>
      match k with
      | 0 => 1
      | 1 => 11 + 2 * A
      | 2 => 55 + 22 * A + A ^ 2
      | 3 => 165 + 110 * A + 11 * A ^ 2
      | 4 => 330 + 330 * A + 55 * A ^ 2
      | 5 => 462 + 660 * A + 165 * A ^ 2
      | 6 => 462 + 924 * A + 330 * A ^ 2
      | 7 => 330 + 924 * A + 462 * A ^ 2
      | 8 => 165 + 660 * A + 462 * A ^ 2
      | 9 => 55 + 330 * A + 330 * A ^ 2
      | 10 => 11 + 110 * A + 165 * A ^ 2
      | 11 => 1 + 22 * A + 55 * A ^ 2
      | 12 => 2 * A + 11 * A ^ 2
      | 13 => A ^ 2
      | _ => 0
    let c : ℕ → ℤ := fun k => (Nat.factorial k) * b k
    ((∀ z : ℤ,
        (1 + A * z) ^ 2 * (1 + z) ^ 11 =
          ∑ degree ∈ Finset.range 14, b degree * z ^ degree) ∧
      Matrix.det (fun i j : Fin 4 => c (3 + j.1 - i.1)) =
        -1584 * (A^8 - 160*A^7 - 300*A^6 - 880*A^5 -
          3410*A^4 - 2640*A^3 - 9900*A^2 - 9075)) := by
  dsimp
  constructor
  · intro z
    norm_num [Finset.sum_range_succ]
    ring
  · have hmatrix :
        (fun i j : Fin 4 =>
          ((Nat.factorial (3 + j.1 - i.1) : ℕ) : ℤ) *
            (match 3 + j.1 - i.1 with
            | 0 => 1
            | 1 => 11 + 2 * A
            | 2 => 55 + 22 * A + A ^ 2
            | 3 => 165 + 110 * A + 11 * A ^ 2
            | 4 => 330 + 330 * A + 55 * A ^ 2
            | 5 => 462 + 660 * A + 165 * A ^ 2
            | 6 => 462 + 924 * A + 330 * A ^ 2
            | 7 => 330 + 924 * A + 462 * A ^ 2
            | 8 => 165 + 660 * A + 462 * A ^ 2
            | 9 => 55 + 330 * A + 330 * A ^ 2
            | 10 => 11 + 110 * A + 165 * A ^ 2
            | 11 => 1 + 22 * A + 55 * A ^ 2
            | 12 => 2 * A + 11 * A ^ 2
            | 13 => A ^ 2
            | _ => 0 : ℤ)) =
          (!![
            (990 + 660*A + 66*A^2), (7920 + 7920*A + 1320*A^2),
              (55440 + 79200*A + 19800*A^2), (332640 + 665280*A + 237600*A^2);
            (110 + 44*A + 2*A^2), (990 + 660*A + 66*A^2),
              (7920 + 7920*A + 1320*A^2), (55440 + 79200*A + 19800*A^2);
            (11 + 2*A), (110 + 44*A + 2*A^2),
              (990 + 660*A + 66*A^2), (7920 + 7920*A + 1320*A^2);
            (1 : ℤ), (11 + 2*A), (110 + 44*A + 2*A^2),
              (990 + 660*A + 66*A^2)] : Matrix (Fin 4) (Fin 4) ℤ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num <;> ring
    rw [hmatrix, Matrix.det_succ_row_zero, Fin.sum_univ_four]
    simp (discharger := decide) [Matrix.det_fin_three, Fin.succAbove]
    ring

end MathlibPlus.Algebra
