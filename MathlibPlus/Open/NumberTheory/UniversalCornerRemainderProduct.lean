import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.NumberTheory

/-- The exact corner remainder-product specification from Claim 8270. -/
def universalCornerRemainderProduct
    (N : ℕ) (χ : DirichletCharacter ℂ N) (w v H : ℂ) : Prop :=
  N > 1 →
    χ (-1 : ZMod N) = (-1 : ℂ) →
    0 < w.re →
    0 < v.re →
    H = ∏' p : {p : ℕ // p.Prime ∧ ¬ p ∣ N},
      (1 - Complex.cpow (p : ℂ) (-1 - w) +
          Complex.cpow (p : ℂ) (-1 - w - v) -
          χ p * Complex.cpow (p : ℂ) (-1 - v)) *
        ((1 - Complex.cpow (p : ℂ) (-1 - w - v)) /
          ((1 - Complex.cpow (p : ℂ) (-1 - w)) *
            (1 - χ p * Complex.cpow (p : ℂ) (-1 - v))))

end MathlibPlus.Open.NumberTheory
