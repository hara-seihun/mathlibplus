import Mathlib

namespace MathlibPlus.Algebra.Claim4827

/-- The even derivative column `g_j = Q'_(2j)` from the Newton square-shift
array.  The polynomial family `Q` is kept as an explicit source carrier. -/
noncomputable def evenDerivativeColumn {R : Type*} [Semiring R]
    (Q : ℕ → Polynomial R) (j : ℕ) : Polynomial R :=
  Polynomial.derivative (Q (2 * j))

end MathlibPlus.Algebra.Claim4827
