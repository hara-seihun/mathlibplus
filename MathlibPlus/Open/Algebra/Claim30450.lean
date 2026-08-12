import Mathlib

namespace MathlibPlus.Open.Algebra.Claim30450

def quarticIrreducibilityClaim30450 : Prop :=
  ∀ d : ℤ, 2 ≤ d →
    Irreducible
      ((Polynomial.X ^ 4 - Polynomial.X ^ 3 +
          Polynomial.C (d : ℚ) * Polynomial.X - 1 : Polynomial ℚ))

end MathlibPlus.Open.Algebra.Claim30450

namespace MathlibPlus.Algebra.Claim30450

open Polynomial

theorem quartic_no_unit_roots_claim30450 (d : ℤ) (hd : 2 ≤ d) :
    let P : Polynomial ℚ := X ^ 4 - X ^ 3 + C (d : ℚ) * X - 1
    P.eval 1 ≠ 0 ∧ P.eval (-1) ≠ 0 := by
  dsimp
  constructor
  · norm_num
    exact_mod_cast (show d - 1 ≠ 0 by omega)
  · norm_num
    intro h
    have h' : (1 : ℚ) - d = 0 := by linarith
    have h'' : (1 : ℤ) - d = 0 := by exact_mod_cast h'
    omega

end MathlibPlus.Algebra.Claim30450
