import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

open scoped BigOperators

namespace MathlibPlus.Algebra.Claim24625And48429

/--
The constant term of a rooted order-`a` context prime is the binomial expression
from claim 48429.  The context tree does not occur in this algebraic identity.
-/
theorem contextPrime_constantTerm {R : Type*} [CommSemiring R]
    (a : ℕ) (ha : 1 ≤ a) (u rho : R) :
    (∑ m ∈ Finset.range a,
      (Nat.choose (a - 1) m : R) * u ^ (a - m) * rho ^ m) =
      u * (u + rho) ^ (a - 1) := by
  rw [add_comm u rho, add_pow]
  simp only [Nat.sub_add_cancel ha]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hm' : m < a := Finset.mem_range.1 hm
  have hpow : a - m = (a - 1 - m) + 1 := by omega
  rw [hpow, pow_succ']
  ring

/--
After the substitutions `y = -z U² + z³ t` and `U = z w`, the top factor
`y + z F_A F_B`, with `F_A = U + z A` and `F_B = U + z B`, has the exact
factorization recorded in claim 24625.
-/
theorem twoScaleNewton_factorization {R : Type*} [CommRing R]
    (A B : Polynomial R) (w t : Polynomial R) :
    (-(Polynomial.X * (Polynomial.X * w) ^ 2) + Polynomial.X ^ 3 * t) +
        Polynomial.X *
          ((Polynomial.X * w + Polynomial.X * A) *
            (Polynomial.X * w + Polynomial.X * B)) =
      Polynomial.X ^ 3 * (t + w * (A + B) + A * B) := by
  ring

end MathlibPlus.Algebra.Claim24625And48429
