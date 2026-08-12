import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MathlibPlus.Algebra

/--
Claim 42809.  Here `T` is the lowering operator on integer-indexed functions
and `d rho` is the displayed operator `(rho + q) T - 1`.  The pointwise form
below is exactly `d rho (1+T) = (1+T) d (rho-1) + T + 2 T^2`, exposing the
source's coefficient `2`.
-/
theorem exactWeightedOperatorIntertwining_claim42809
    {R : Type*} [CommRing R] (rho : R) (f : ℤ → R) :
    let T : (ℤ → R) → (ℤ → R) := fun g q => g (q - 1)
    let d : R → (ℤ → R) → (ℤ → R) :=
      fun r g q => (r + (q : R)) * g (q - 1) - g q
    ∀ q : ℤ,
      d rho (f + T f) q =
        (d (rho - 1) f q + T (d (rho - 1) f) q) + T f q +
          2 * T (T f) q := by
  dsimp
  intro q
  norm_num [Int.cast_add, Int.cast_neg, Int.cast_one]
  ring

end MathlibPlus.Algebra
