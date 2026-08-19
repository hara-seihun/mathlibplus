import MathlibPlus.Open.ResearchFormalization.R1247.Claim30569

namespace MathlibPlus.Open.ResearchFormalization.R1247.Claim30563

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1247.Claim30569

abbrev GroupCarrier (p : ℕ) := V p × SectionLabel

private def markedMap (p : ℕ) : GroupCarrier p → GroupCarrier p :=
  fun v => (sectionShear p v.2 v.1, v.2)

/-- Claim 30563: the parity-mixed marked map on `V = F_p^2` and the three
rotation/three reflection sections uses the exact quadratic shears and has
identity base permutation. -/
def markedMapSpecification_claim30563 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → Odd p →
    (∀ v : V p,
      shearA p v = (v.1, v.2 + binomialTwo p v.1) ∧
        shearB p v = (v.1 + binomialTwo p v.2, v.2)) ∧
    (∀ h : SectionLabel, rotationSection h →
      ∀ v : V p, markedMap p (v, h) = (shearA p v, h)) ∧
    (∀ h : SectionLabel, reflectionSection h →
      ∀ v : V p, markedMap p (v, h) = (shearB p v, h)) ∧
    (∀ v : GroupCarrier p, (markedMap p v).2 = v.2)

end

end MathlibPlus.Open.ResearchFormalization.R1247.Claim30563
