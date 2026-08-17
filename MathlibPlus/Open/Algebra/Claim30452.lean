import Mathlib
import MathlibPlus.Open.Research.R1238

namespace MathlibPlus.Open.Algebra.Claim30452

noncomputable section

open MathlibPlus.Open.Research.R1238
open Polynomial

/-- The common-root carrier supplied by the two short-leaf factors. -/
def commonRoot (a b : ℕ) (α : ℂ) : Prop :=
  aeval α (shortLeafA a b) = 0 ∧
    aeval α (shortLeafB a b) = 0

/-- Claim 30452: at a common root of the displayed short-leaf factors, the
shift `t = α + 1` satisfies the displayed arm equation. -/
def claim30452_shiftedArmEquation : Prop :=
  ∀ (a b : ℕ), 1 ≤ a →
    ∀ (α : ℂ), commonRoot a b α →
      let t : ℂ := α + 1
      t ^ ((a : ℤ) - 2) * (t ^ 2 - t + 1) ^ b =
        -(t - 1) ^ ((a : ℤ) + 2 * (b : ℤ))

end

end MathlibPlus.Open.Algebra.Claim30452
