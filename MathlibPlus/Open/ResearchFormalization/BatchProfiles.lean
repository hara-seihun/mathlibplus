import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchProfiles

abbrev F5 := ZMod 5
abbrev SixSpace := Fin 6 → F5
abbrev FourFlat := {U : Submodule F5 SixSpace // Module.finrank F5 U = 4}

noncomputable def fourFlatProfile (S : Set SixSpace) : Multiset ℕ := by
  classical
  exact
    (Finset.univ : Finset FourFlat).val.map
      (fun U =>
        (Finset.univ.filter
          (fun x : SixSpace => x ∈ S ∩ (U.1 : Set SixSpace))).card)

/-- The multiset of four-flat intersection sizes is invariant under the
natural `GL₆(F₅)` action. -/
def projectiveFourFlatIncidenceProfile : Prop :=
  ∀ (S T : Set SixSpace) (g : SixSpace ≃ₗ[F5] SixSpace),
    0 ∉ S → g '' S = T → fourFlatProfile S = fourFlatProfile T

end MathlibPlus.Open.ResearchFormalization.BatchProfiles
