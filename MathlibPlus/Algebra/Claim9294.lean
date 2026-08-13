import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic

namespace MathlibPlus.Algebra.Claim9294

open Polynomial

/--
Claim 9294: after the reciprocal-trace substitutions, the bridge relation is
`2 r - (t + 2) q = t ell`.  The source defines the correction by
`q = ell - 2 c` and `r = (t + 1) q + t c`; those definitions are made
explicit here rather than introducing an unspecified trace interface.
-/
theorem traceCoordinateLinearRelation_claim9294
    (ell c : ℤ[X]) :
    let q := ell - 2 * c
    let r := (X + 1) * q + X * c
    2 * r - (X + 2) * q = X * ell := by
  dsimp
  ring

/--
Under the source's correction equation `ell = q + 2 c`, the displayed bridge
relation is equivalent to the displayed formula for `r`.
-/
theorem traceCoordinateLinearRelation_iff_claim9294
    {ell q r c : ℤ[X]}
    (hEll : ell = q + 2 * c) :
    (2 * r - (X + 2) * q = X * ell) ↔
      r = (X + 1) * q + X * c := by
  constructor
  · intro h
    have h2 : (2 : ℤ[X]) * r = 2 * ((X + 1) * q + X * c) := by
      calc
        2 * r = (X + 2) * q + X * ell := by
          linear_combination h
        _ = 2 * ((X + 1) * q + X * c) := by
          rw [hEll]
          ring
    exact mul_left_cancel₀ (by norm_num : (2 : ℤ[X]) ≠ 0) h2
  · intro hr
    rw [hr, hEll]
    ring

end MathlibPlus.Algebra.Claim9294
