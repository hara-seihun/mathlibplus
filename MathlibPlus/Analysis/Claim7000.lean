import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace MathlibPlus.Analysis.Claim7000

/--
The displayed degree-one scalar from claim 7000 is preserved by the source's
coordinate substitutions `z = s - 1` and `α = s + k - 1`, under the real
`rpow` interpretation of the exponential factor.
-/
theorem minimalPSSScalarFactor_claim7000 (s k : ℝ) :
    let A : ℝ → ℝ → ℝ := fun k z => (2 : ℝ) ^ (1 - z) / (z + k)
    let z := s - 1
    let α := s + k - 1
    A k z = (2 : ℝ) ^ (2 - s) / α := by
  dsimp
  have hs : 1 - (s - 1) = 2 - s := by ring
  have hk : (s - 1) + k = s + k - 1 := by ring
  rw [hs, hk]

