import MathlibPlus.Open.ResearchFormalization.R0992Claim28032
import MathlibPlus.Open.Research.OrbitalCriteria

namespace MathlibPlus.Open.ResearchFormalization.R0992Claim28039

open MathlibPlus.Open.ResearchFormalization.R0992Claim28032
open MathlibPlus.Open.Research.OrbitalCriteria

noncomputable section

/-- The exact internal-conjugacy conclusion for the displayed pair. -/
def displayedPairHarmless (F : Plane → Fibre) : Prop :=
  let q := transporter F
  let G := generatedGroup q
  ∃ c : Equiv.Perm E,
    c ∈ twoClosureOf (G : Set (Equiv.Perm E)) ∧
      Set.image (fun h => c⁻¹ * h * c)
          (translationGroup : Set (Equiv.Perm E)) =
        transportedTranslations q

/-- Claim 28039: every coefficient table in the fixed homogeneous family
has the displayed regular pair conjugate inside the exact 2-closure. -/
def claim28039 : Prop :=
  (∀ F : Plane → Fibre, displayedPairHarmless F) ∧
    Fintype.card (Plane → Fibre) = 27 ^ 9 ∧
      27 ^ 9 = 3 ^ 27 ∧
        3 ^ 27 = 7625597484987

end
end MathlibPlus.Open.ResearchFormalization.R0992Claim28039
