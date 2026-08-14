import Mathlib

open scoped BigOperators
open Classical
noncomputable section

namespace MathlibPlus.Open.Research.ComponentRegimes

/-- Claim 35239: the balanced three-part component regime. -/
def balanced_three_part_component_regime (n : ℕ) (parts : Multiset ℕ) : Prop :=
  parts.card = 3 ∧ parts.sum = n ∧ ∀ a ∈ parts, 2 ≤ a ∧ a ≤ n / 2

end MathlibPlus.Open.Research.ComponentRegimes
