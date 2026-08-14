import Mathlib

namespace MathlibPlus.Open.O0185

/-- The discriminant polynomial from Claim 14845. -/
def discriminant (p q r : ℂ) : ℂ :=
  q ^ 2 - 16 * p - q ^ 3 * r + 18 * p * q * r - 27 * p ^ 2 * r ^ 2

/-- The discriminant hypersurface from Claim 14845. -/
def Sigma : Set (ℂ × ℂ × ℂ) :=
  {v | discriminant v.1 v.2.1 v.2.2 = 0}

/-- The triple-root curve from Claim 14845. -/
def Gamma : Set (ℂ × ℂ × ℂ) :=
  {v | 12 * v.1 - v.2.1 ^ 2 = 0 ∧ 3 * v.2.1 * v.2.2 - 4 = 0}

end MathlibPlus.Open.O0185
