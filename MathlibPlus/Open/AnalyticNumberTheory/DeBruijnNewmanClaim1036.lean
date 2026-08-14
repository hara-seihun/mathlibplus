import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory

/-!
# Repaired de Bruijn--Newman upper-bound carrier

The source's Polymath15 normalization supplies a scalar `Λ` but no canonical
project declaration for that invariant, so it remains an explicit carrier.
-/

/-- Claim 1036: in the stated normalization, the unconditional repaired upper
bound is `Λ ≤ 7/40 = 0.175`. -/
def strongerDeBruijnNewmanUpperBound_claim1036 (Λ : ℝ) : Prop :=
  Λ ≤ (7 / 40 : ℝ) ∧ (7 / 40 : ℝ) = 175 / 1000

end MathlibPlus.Open.AnalyticNumberTheory
