import Mathlib

namespace MathlibPlus.Combinatorics

/-!
# Frequency deficit

The finite-family definition from admitted claim 20526 is recorded with an
arbitrary type of coordinates and finite families of finite subsets.  The
codomain is `ℤ`, since the deficit need not be nonnegative.
-/

/-- Claim 20526: the deficit of coordinate `x` in finite family `A`. -/
def frequencyDeficit {α : Type*} [DecidableEq α]
    (A : Finset (Finset α)) (x : α) : ℤ :=
  (A.card : ℤ) - 2 * ((A.filter (fun S => x ∈ S)).card : ℤ)

end MathlibPlus.Combinatorics
