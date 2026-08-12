import Mathlib

namespace MathlibPlus.Combinatorics.Claim52187

/-- The four rooted messages of the five-vertex spider `S(1,1,2)`, built from
its rooted-message recursion `B_R = v + u * ∏ B_child`.  The variables are
represented by the outer polynomial `u` and the coefficient polynomial `v`.
-/
theorem orderFiveRootedMessages :
    let u : MvPolynomial (Fin 2) ℤ := MvPolynomial.X 0
    let v : MvPolynomial (Fin 2) ℤ := MvPolynomial.X 1
    let leaf : MvPolynomial (Fin 2) ℤ := v + u
    let path : MvPolynomial (Fin 2) ℤ := v + u * leaf
    let center : MvPolynomial (Fin 2) ℤ := v + u * leaf ^ 2
    let bCenter : MvPolynomial (Fin 2) ℤ := v + u * (leaf ^ 2 * path)
    let bLong : MvPolynomial (Fin 2) ℤ :=
      v + u * (v + u * center)
    let bMiddle : MvPolynomial (Fin 2) ℤ := v + u * (center * leaf)
    let bShort : MvPolynomial (Fin 2) ℤ :=
      v + u * (v + u * (leaf * path))
    bCenter = v + u * v ^ 3 + u ^ 2 * (2 * v ^ 2 + v ^ 3) +
        u ^ 3 * (v + 3 * v ^ 2) + 3 * u ^ 4 * v + u ^ 5 ∧
      bLong = v + u * v + u ^ 2 * v + u ^ 3 * v ^ 2 +
        2 * u ^ 4 * v + u ^ 5 ∧
      bMiddle = v + u * v ^ 2 + u ^ 2 * (v + v ^ 3) +
        3 * u ^ 3 * v ^ 2 + 3 * u ^ 4 * v + u ^ 5 ∧
      bShort = v + u * v + u ^ 2 * v ^ 2 +
        u ^ 3 * (v + v ^ 2) + 2 * u ^ 4 * v + u ^ 5 := by
  dsimp
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  · ring

end MathlibPlus.Combinatorics.Claim52187
