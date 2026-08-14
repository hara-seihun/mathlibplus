import Mathlib

namespace MathlibPlus.Algebra.Claim27079

/--
The exact collar expansion of the weight-six product secant from claim 27079,
after expanding the rooted-factor recursion.  Here `ell k` is `x_(k+1) -
z * x_k`; the identity is purely polynomial and therefore holds over every
commutative ring.
-/
theorem productSecantCollarExpansion_claim27079
    {R : Type*} [CommRing R] (z x1 x2 x3 x4 x5 : R) :
    let S1 := x1 + z
    let S2 := x2 + x1 ^ 2 + z * x1 + z ^ 2
    let U5 :=
      x5 + 2 * (x2 * x3) + 2 * (x1 * x4) + 3 * (x1 * x2 ^ 2) +
        3 * (x1 ^ 2 * x3) + z * x1 * x3 + z ^ 2 * x3 +
        4 * (x1 ^ 3 * x2) + 2 * (z * x1 ^ 2 * x2) +
        3 * (z ^ 2 * x1 * x2) + z ^ 3 * x2 + x1 ^ 5 +
        z * x1 ^ 4 + 2 * (z ^ 2 * x1 ^ 3) +
        2 * (z ^ 3 * x1 ^ 2) + 2 * (z ^ 4 * x1) + z ^ 5
    let V4 :=
      x4 + 3 * (x1 * x3) + z * x3 + 3 * (x1 ^ 2 * x2) +
        2 * (z * x1 * x2) + x1 ^ 4 + z * x1 ^ 3 +
        z ^ 2 * x1 ^ 2 + 2 * (z ^ 3 * x1) + z ^ 4
    let ell1 := x2 - z * x1
    let ell2 := x3 - z * x2
    let ell3 := x4 - z * x3
    let ell4 := x5 - z * x4
    S1 * U5 - S2 * V4 =
      -x1 * ell1 * ell2 + (x1 * S1 - ell1) * ell3 + S1 * ell4 := by
  dsimp
  ring

/-- The displayed product secant is not the zero symbolic polynomial. -/
theorem productSecantDifference_symbolic_ne_zero_claim27079 :
    let z : MvPolynomial (Fin 6) ℚ := MvPolynomial.X 0
    let x1 : MvPolynomial (Fin 6) ℚ := MvPolynomial.X 1
    let x2 : MvPolynomial (Fin 6) ℚ := MvPolynomial.X 2
    let x3 : MvPolynomial (Fin 6) ℚ := MvPolynomial.X 3
    let x4 : MvPolynomial (Fin 6) ℚ := MvPolynomial.X 4
    let x5 : MvPolynomial (Fin 6) ℚ := MvPolynomial.X 5
    let S1 := x1 + z
    let S2 := x2 + x1 ^ 2 + z * x1 + z ^ 2
    let U5 :=
      x5 + 2 * (x2 * x3) + 2 * (x1 * x4) + 3 * (x1 * x2 ^ 2) +
        3 * (x1 ^ 2 * x3) + z * x1 * x3 + z ^ 2 * x3 +
        4 * (x1 ^ 3 * x2) + 2 * (z * x1 ^ 2 * x2) +
        3 * (z ^ 2 * x1 * x2) + z ^ 3 * x2 + x1 ^ 5 +
        z * x1 ^ 4 + 2 * (z ^ 2 * x1 ^ 3) +
        2 * (z ^ 3 * x1 ^ 2) + 2 * (z ^ 4 * x1) + z ^ 5
    let V4 :=
      x4 + 3 * (x1 * x3) + z * x3 + 3 * (x1 ^ 2 * x2) +
        2 * (z * x1 * x2) + x1 ^ 4 + z * x1 ^ 3 +
        z ^ 2 * x1 ^ 2 + 2 * (z ^ 3 * x1) + z ^ 4
    S1 * U5 - S2 * V4 ≠ 0 := by
  dsimp
  intro h
  have h_eval := congrArg
      (MvPolynomial.eval
        (fun i : Fin 6 => if i.val = 1 ∨ i.val = 5 then (1 : ℚ) else 0)) h
  norm_num [MvPolynomial.eval_add, MvPolynomial.eval_sub,
    MvPolynomial.eval_mul, MvPolynomial.eval_pow] at h_eval

end MathlibPlus.Algebra.Claim27079
