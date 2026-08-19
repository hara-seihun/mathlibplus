import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2662Claim42233

/-- Claim 42233: the exact outside-support profile is strictly smaller than
its ambient exact-three-tight family size for every natural k. -/
def claim42233 : Prop :=
  ∀ k : ℕ, k + 4 < 2 * k + 17

end MathlibPlus.Open.ResearchFormalization.R2662Claim42233
