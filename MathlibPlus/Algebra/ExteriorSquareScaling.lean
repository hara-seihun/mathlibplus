import Mathlib

namespace MathlibPlus.Algebra.ExteriorSquareScaling

/-- Claim 4471: for a finite collection of geometric modes, multiplying every
coefficient by `c` multiplies the adjacent exterior square by `c^2`; the
special case `c = -1` records the phase/sign cancellation explicitly. -/
theorem finiteExteriorSquare_scale_claim4471
    {n : ℕ} (a b : Fin n → ℂ) (c : ℂ) (r : ℕ) :
    let G : (Fin n → ℂ) → ℕ → ℂ :=
      fun coeff k => ∑ j : Fin n, coeff j * b j ^ k
    let H : (Fin n → ℂ) → ℕ → ℂ :=
      fun coeff k => G coeff k * G coeff (k + 2) - (G coeff (k + 1)) ^ 2
    H (fun j => c * a j) r = c ^ 2 * H a r ∧
      H (fun j => -a j) r = H a r := by
  dsimp
  have hG (k : ℕ) :
      (∑ j : Fin n, (c * a j) * b j ^ k) =
        c * (∑ j : Fin n, a j * b j ^ k) := by
    calc
      (∑ j : Fin n, (c * a j) * b j ^ k) =
          ∑ j : Fin n, c * (a j * b j ^ k) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = c * (∑ j : Fin n, a j * b j ^ k) := by
        symm
        simpa using
          (Finset.mul_sum Finset.univ (fun j : Fin n => a j * b j ^ k) c)
  constructor
  · rw [hG r, hG (r + 2), hG (r + 1)]
    ring
  · have hGneg (k : ℕ) :
        (∑ j : Fin n, (-a j) * b j ^ k) =
          -(∑ j : Fin n, a j * b j ^ k) := by
      calc
        (∑ j : Fin n, (-a j) * b j ^ k) =
            ∑ j : Fin n, -(a j * b j ^ k) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
        _ = -(∑ j : Fin n, a j * b j ^ k) := by
          rw [← Finset.sum_neg_distrib]
    rw [hGneg r, hGneg (r + 2), hGneg (r + 1)]
    ring

end MathlibPlus.Algebra.ExteriorSquareScaling
