import Mathlib

namespace MathlibPlus.Open.NewResearch2.FormalizationDrain019ffc
namespace C0091

/-- Claim 1399: the endpoint constants lie in the certified decimal
enclosures recorded in the packet, including the scaled alpha enclosure. -/
def claim1399 (alpha beta delta : ℝ) : Prop :=
  alpha ∈ Set.Icc
      0.072815845483676724860586375874901319
      (0.072815845483676724860586375874901319 + 1 / (10 : ℝ) ^ 36) ∧
    151 * alpha ∈ Set.Icc
      10.995192668035185453948542757110099189
      (10.995192668035185453948542757110099189 + 1 / (10 : ℝ) ^ 36) ∧
    beta ∈ Set.Icc 0.1330804185339663023
      (0.1330804185339663023 + 1 / (10 : ℝ) ^ 19) ∧
    delta ∈ Set.Icc 0.0318133338179058966
      (0.0318133338179058966 + 1 / (10 : ℝ) ^ 19)

end C0091
end MathlibPlus.Open.NewResearch2.FormalizationDrain019ffc
