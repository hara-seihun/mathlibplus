import MathlibPlus.Open.ResearchFormalization.R1247.Claim30569
import MathlibPlus.Open.ResearchFormalization.R1247.Claim30571

namespace MathlibPlus.Open.ResearchFormalization.R1247RelativeDerivative

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1247.Claim30569

/-- Claim 30564: compute the relative derivative from the actual marked map
on `V × S₃`, rather than assuming section preservation in its generator.  The
computed map preserves the section label and has the reviewed sectionwise
formula. -/
def actualRelativeDerivativeHasSectionFormula_claim30564 : Prop :=
  ∀ p : ℕ, Nat.Prime p → Odd p →
    let Point := V p × SectionLabel
    let markedMap : Point → Point :=
      fun z => (sectionShear p z.2 z.1, z.2)
    ∀ (u : V p) (k : SectionLabel),
      let relativePoint : Point → Point :=
        fun z =>
          let image := markedMap (z.1 + u, z.2 * k)
          let anchor := markedMap (u, k)
          (sectionShearInverse p z.2 (image.1 - anchor.1), z.2)
      ∀ (v : V p) (h : SectionLabel),
        (relativePoint (v, h)).2 = h ∧
          relativePoint (v, h) =
            (relativeDerivative p u k h v, h)

end

end MathlibPlus.Open.ResearchFormalization.R1247RelativeDerivative
