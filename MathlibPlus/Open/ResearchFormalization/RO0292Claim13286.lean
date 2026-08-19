import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.RO0292Claim13286

/-- Claim 13286: the endpoint witness set `E = {1 + 1/n | n ≥ 1}` is
contained in the open half-line `(1, ∞)`. -/
def endpointCounterexampleSet_subset_Ioi_one_claim13286 : Prop :=
  let E : Set ℝ :=
    {x : ℝ | ∃ n : ℕ, 1 ≤ n ∧ x = 1 + 1 / (n : ℝ)}
  E ⊆ Set.Ioi (1 : ℝ)

end MathlibPlus.Open.ResearchFormalization.RO0292Claim13286
