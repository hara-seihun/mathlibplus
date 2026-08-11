import Mathlib

/-!
# Interval reflection

Admitted claim 6846 states the coordinate identity for reflection. Since the
packet does not fix a truncated-natural-number convention, this formalization
uses integer coordinates and records the pair relation explicitly.
-/

namespace MathlibPlus.Algebra.IntervalReflection

/-- Reflection in the midpoint of the interval with endpoint sum `a + b - 1`. -/
def reflect (a b i : ℤ) : ℤ := a + b - 1 - i

theorem reflect_pair (a b p q : ℤ) (hpq : p + q = a + b - 1) :
    (reflect a b p, reflect a b q) = (q, p) := by
  apply Prod.ext <;> dsimp [reflect] <;> omega

end MathlibPlus.Algebra.IntervalReflection
