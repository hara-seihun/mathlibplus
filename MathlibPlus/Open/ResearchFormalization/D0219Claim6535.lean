import MathlibPlus.Open.ResearchFormalizationBlocks
import MathlibPlus.Open.Research.AdmittedBlocks

namespace MathlibPlus.Open.ResearchFormalization.D0219Claim6535

open MathlibPlus.Open.ResearchFormalizationBlocks
open MathlibPlus.Open.ResearchBlocks

/-- Claim 6535: a base-fixing profile changes a cross-block fibre difference
by the profile difference, and off-diagonal saturation makes that shift
allowed. -/
def profilesChangeCrossBlockDifference_claim6535 : Prop :=
  ∀ {β : Type*} [Fintype β]
    (H : Subgroup (Equiv.Perm (BlockVertex β)))
    (hInvariant : blockSystemInvariant H)
    (hRegular : regularFibreTranslations H)
    (p : β → Fibre),
    offDiagonalSaturation H hInvariant hRegular →
      ∀ B C : β, B ≠ C →
        p C - p B ∈ allowedShiftSpace H B C ∧
          ∀ d e : Fibre,
            (profileMap p (e, C)).1 - (profileMap p (d, B)).1 =
              (e - d) + (p C - p B)

end MathlibPlus.Open.ResearchFormalization.D0219Claim6535
