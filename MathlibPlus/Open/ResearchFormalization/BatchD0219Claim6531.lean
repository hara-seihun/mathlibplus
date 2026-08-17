import Mathlib
import MathlibPlus.Open.ResearchFormalizationBlocks

namespace MathlibPlus.Open.ResearchFormalization.D0219Claim6531

open MathlibPlus.Open.ResearchFormalizationBlocks

/-- Claim 6531: the allowed-shift space is the set of fibre shifts whose
translated ordered pair is in the same `H`-orbital for every fibre point. -/
def allowedShiftSpaceClaim6531 {β : Type*}
    (H : Subgroup (Equiv.Perm (BlockVertex β)))
    (B C : β) : Set Fibre :=
  {a | ∀ x : Fibre,
    sameHOrbital H ((0, B), (x, C)) ((0, B), (x + a, C))}

end MathlibPlus.Open.ResearchFormalization.D0219Claim6531
