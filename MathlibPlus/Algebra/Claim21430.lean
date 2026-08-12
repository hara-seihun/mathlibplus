import Mathlib

namespace MathlibPlus.Algebra.Claim21430

/-- The displayed `L_r = 2r+1+a_r` substitution gives the source's
four-offset decomposition of the Record-12 left side. -/
theorem record12_left_side_decomposition
    {R : Type*} [CommRing R] (e : ℤ → R) (a_r L_r : R) (k r : ℤ)
    (hL : L_r = 2 * (r : R) + 1 + a_r) :
    e (k + r + 1) - e (k - r) - L_r * (e (k + 1) - e k) =
      (e (k + r + 1) - e (k - r) -
          (2 * (r : R) + 1) * (e (k + 1) - e k)) -
        a_r * (e (k + 1) - e k) := by
  rw [hL]
  ring

/-- The four-offset part `C_{k,r}` annihilates every affine offset sequence.
The integer index type makes the source's occurrences of `k-r` literal. -/
theorem affine_offset_cancellation
    {R : Type*} [CommRing R] (α β : R) (k r : ℤ) :
    let e : ℤ → R := fun n => α * (n : R) + β
    e (k + r + 1) - e (k - r) -
        (2 * (r : R) + 1) * (e (k + 1) - e k) = 0 := by
  dsimp
  simp only [Int.cast_add, Int.cast_sub, Int.cast_one]
  ring

end MathlibPlus.Algebra.Claim21430
