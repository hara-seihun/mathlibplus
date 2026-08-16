import Mathlib

open scoped BigOperators

namespace MathlibPlus
namespace Open
namespace ResearchFormalization

noncomputable section

/-- The variables `z,x₁,x₂,...` are represented by natural-number variables,
with `0` reserved for `z`. -/
def geometricTailVariable (j : ℕ) : MvPolynomial ℕ ℚ :=
  MvPolynomial.X j

def geometricTailTargetVariable (j : Fin 3) : MvPolynomial (Fin 3) ℚ :=
  MvPolynomial.X j

def geometricTailImage (j : ℕ) : MvPolynomial (Fin 3) ℚ :=
  match j with
  | 0 => geometricTailTargetVariable 0
  | 1 => geometricTailTargetVariable 1
  | n + 2 => (geometricTailTargetVariable 0) ^ n * geometricTailTargetVariable 2

def geometricTailQuotient :
    MvPolynomial ℕ ℚ →+* MvPolynomial (Fin 3) ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C geometricTailImage

def geometricTailIdeal : Ideal (MvPolynomial ℕ ℚ) :=
  Ideal.span {p | ∃ j : ℕ, 2 ≤ j ∧
    p = geometricTailVariable (j + 1) -
      geometricTailVariable 0 * geometricTailVariable j}

def claim25119 : Prop :=
  (∀ j : ℕ, 2 ≤ j →
    geometricTailQuotient (geometricTailVariable j) =
      (geometricTailTargetVariable 0) ^ (j - 2) * geometricTailTargetVariable 2) ∧
  RingHom.ker geometricTailQuotient = geometricTailIdeal ∧
  geometricTailIdeal.IsPrime

end
end ResearchFormalization
end Open
end MathlibPlus
