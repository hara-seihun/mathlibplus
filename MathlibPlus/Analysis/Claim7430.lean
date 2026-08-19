import Mathlib

namespace MathlibPlus.Analysis

/-- The normalized two-sheet spectral coordinate from K-0010, with the
constant `a = 5/4` fixed as in the source. -/
noncomputable def claim7430P (t q : ℝ) : ℝ :=
  Real.cosh t + Real.sinh t * Real.tanh ((5 / 4 : ℝ) * t - q * Real.sinh t)

/-- Proof-free registry assertion for the derivative form of the logistic
law. -/
def claim7430P_hasDerivAt : Prop :=
  ∀ (t q : ℝ),
    HasDerivAt (fun q' => claim7430P t q')
      (-Real.sinh t * Real.sinh t /
        Real.cosh ((5 / 4 : ℝ) * t - q * Real.sinh t) ^ 2) q

/-- Proof-free registry assertion for the factorized Riccati form of the
same normalized coordinate law. -/
def claim7430_riccati : Prop :=
  ∀ (t q : ℝ),
    deriv (fun q' => claim7430P t q') q =
      -(claim7430P t q - Real.exp (-t)) *
        (Real.exp t - claim7430P t q)

end MathlibPlus.Analysis
