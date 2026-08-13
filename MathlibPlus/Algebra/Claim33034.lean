import Mathlib

namespace MathlibPlus.Algebra.Claim33034

private lemma two_isUnit_of_odd_char (R : Type*) [CommRing R] (p : ℕ)
    [CharP R p] (hp : Odd p) : IsUnit (2 : R) := by
  rcases hp with ⟨k, hk⟩
  apply IsUnit.of_mul_eq_one (k + 1 : R)
  have hpk : (2 : R) * (k : R) + 1 = 0 := by
    calc
      (2 : R) * (k : R) + 1 = ((2 * k + 1 : ℕ) : R) := by push_cast; ring
      _ = (p : R) := by rw [hk]
      _ = 0 := CharP.cast_eq_zero R p
  calc
    (2 : R) * (k + 1 : R) = (2 : R) * (k : R) + 1 + 1 := by
      ring
    _ = 0 + 1 := by rw [hpk]
    _ = 1 := by ring

/-- Polarization of the square map in a commutative ring. -/
theorem polarization_square_zero (R : Type*) [CommRing R] (x y : R) :
    (2 : R) * (x * y) = (x + y) ^ 2 - x ^ 2 - y ^ 2 := by
  ring

/-- In odd characteristic, a commutative algebra whose every square is zero has
zero multiplication. -/
theorem oddCharacteristicSquareZero_mul_eq_zero
    (R : Type*) [CommRing R] (p : ℕ) [CharP R p] (hp : Odd p)
    (hsq : ∀ x : R, x ^ 2 = 0) : ∀ x y : R, x * y = 0 := by
  have h2 : IsUnit (2 : R) := two_isUnit_of_odd_char R p hp
  intro x y
  have hpolar : (2 : R) * (x * y) = 0 := by
    calc
      (2 : R) * (x * y) = (x + y) ^ 2 - x ^ 2 - y ^ 2 :=
        polarization_square_zero R x y
      _ = 0 := by rw [hsq, hsq, hsq]; ring
  apply h2.mul_left_cancel
  simpa using hpolar

end MathlibPlus.Algebra.Claim33034
