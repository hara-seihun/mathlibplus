import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Polynomial

namespace MathlibPlus.Algebra.Claim24468

/-!
Formalization of the coefficient statement in admitted claim 24468 (packet
`R-0756`).  For a fixed `i`, the source expression `A_i = x_m + a_i` is
represented by the polynomial `X + C a` in the formal variable `x_m`; the
coefficient ring is kept generic so that `a_i` may itself be a lower-variable
polynomial.
-/

/-- The three displayed coefficients of the equal pure power `A_i^d`. -/
theorem topThreeCoefficients {R : Type*} [CommSemiring R]
    (a : R) (d : ℕ) (hd : 2 ≤ d) :
    ((X + C a) ^ d).coeff d = 1 ∧
      ((X + C a) ^ d).coeff (d - 1) = (d : R) * a ∧
      ((X + C a) ^ d).coeff (d - 2) = (d.choose 2 : R) * a ^ 2 := by
  have h₁ : d.choose (d - 1) = d := by
    rw [Nat.choose_symm (by omega), Nat.choose_one_right]
  have h₂ : d.choose (d - 2) = d.choose 2 := by
    rw [Nat.choose_symm (by omega)]
  have hself : d.choose d = 1 := Nat.choose_self d
  have hsub₁ : d - (d - 1) = 1 := by omega
  have hsub₂ : d - (d - 2) = 2 := by omega
  rw [Polynomial.coeff_X_add_C_pow, Polynomial.coeff_X_add_C_pow,
    Polynomial.coeff_X_add_C_pow]
  simp only [Nat.sub_self, pow_zero, one_mul, hself, h₁, h₂, hsub₁, hsub₂]
  ring_nf
  simp

end MathlibPlus.Algebra.Claim24468
