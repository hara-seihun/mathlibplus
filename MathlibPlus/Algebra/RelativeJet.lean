import Mathlib.Algebra.Ring.Defs

namespace MathlibPlus.Algebra.RelativeJet

theorem exchange_power_parity
    {M R : Type*} [Ring R] (e : M → M) (ell : M → R)
    (_hinv : ∀ m, e (e m) = m)
    (hodd : ∀ m, ell (e m) = -ell m) (r : ℕ) :
    (fun m => ell (e m) ^ r) =
      (fun m => (-1 : R) ^ r * ell m ^ r) := by
  funext m
  rw [hodd]
  induction r with
  | zero => simp
  | succ r ih =>
    calc
      (-ell m) ^ (r + 1) = (-ell m) ^ r * (-ell m) := by rw [pow_succ]
      _ = ((-1 : R) ^ r * ell m ^ r) * (-ell m) := by rw [ih]
      _ = (-1 : R) ^ (r + 1) * ell m ^ (r + 1) := by
        simp only [pow_succ]
        simp [mul_assoc]

end MathlibPlus.Algebra.RelativeJet
