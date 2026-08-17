import MathlibPlus.Open.ResearchFormalization.R1164FullSuborbit

namespace MathlibPlus.Open.ResearchFormalization.R1164Claims31734_41496

open MathlibPlus.Open.ResearchFormalizationBatch_01a000eb
open MathlibPlus.Open.ResearchFormalization.R1164

/-- Claim 31734: every retained displayed transporter moves a point-stabilizer
suborbit and lies outside the generated two-closure. -/
def claim31734 : Prop :=
  MathlibPlus.Open.ResearchFormalization.R1164.claim41498

/-- Claim 41496: the retained nonlinear periodic rows have cardinality 50,262,
and each displayed normalized transporter fixes the zero point.  The exact
translation-pair group and displayed transporter are the imported
`r1164GeneratedGroup` and `r1164DisplayedTransporter` definitions on the
`RankFiveE` carrier. -/
def claim41496 : Prop :=
  r1164RetainedCount = 50262 ∧
    ∀ r : R1164RetainedRow,
      r1164DisplayedTransporter r rankFiveZero = rankFiveZero

end MathlibPlus.Open.ResearchFormalization.R1164Claims31734_41496
