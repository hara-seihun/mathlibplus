import Mathlib

namespace MathlibPlus.Algebra.Claim32397

noncomputable section

local notation "R" => Polynomial (Polynomial (ZMod 2))
local notation "u" => (Polynomial.X : R)
local notation "r" => (Polynomial.C (Polynomial.X : Polynomial (ZMod 2)) : R)
local notation "s" => u + r

private lemma s_nonzero : s ≠ 0 := by
  exact Polynomial.X_add_C_ne_zero _

private lemma r_nonzero : r ≠ 0 := by
  exact Polynomial.C_ne_zero.mpr Polynomial.X_ne_zero

theorem parityCoreCoefficient_spec (ell : ℕ) :
    (Even ell → s ^ ell ≠ 0) ∧
    (Odd ell → r * s ^ (ell - 1) ≠ 0) := by
  constructor
  · intro hell
    exact pow_ne_zero _ s_nonzero
  · intro holl
    exact mul_ne_zero r_nonzero (pow_ne_zero _ s_nonzero)

/-- A polynomial in the auxiliary variable `w` is nonzero when its coefficient
of `w^(ell+1)` is the parity-core factor from the packet. -/
theorem nonzero_of_parity_core_coefficient
    (ell : ℕ) (E_H : Polynomial R)
    (hcoeff : E_H.coeff (ell + 1) =
      if Even ell then s ^ ell else r * s ^ (ell - 1)) :
    E_H ≠ 0 := by
  by_cases hell : Even ell
  · have hfactor : s ^ ell ≠ 0 := pow_ne_zero _ s_nonzero
    intro hE
    apply hfactor
    calc
      s ^ ell = (if Even ell then s ^ ell else r * s ^ (ell - 1)) := by
        simp [hell]
      _ = E_H.coeff (ell + 1) := hcoeff.symm
      _ = 0 := by simp [hE]
  · have hfactor : r * s ^ (ell - 1) ≠ 0 :=
      mul_ne_zero r_nonzero (pow_ne_zero _ s_nonzero)
    intro hE
    apply hfactor
    calc
      r * s ^ (ell - 1) =
          (if Even ell then s ^ ell else r * s ^ (ell - 1)) := by
        simp [hell]
      _ = E_H.coeff (ell + 1) := hcoeff.symm
      _ = 0 := by simp [hE]

end
end MathlibPlus.Algebra.Claim32397
