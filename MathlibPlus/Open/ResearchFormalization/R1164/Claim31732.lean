import MathlibPlus.Open.ResearchFormalization.R1164FullSuborbit

namespace MathlibPlus.Open.ResearchFormalization.R1164

open MathlibPlus.Open.ResearchFormalizationBatch_01a000eb

/-- Claim 31732: the retained normalized nonlinear rows have cardinality
    50,262, and every displayed transporter fixes the normalized zero point.
    The retained-row, transporter, translation-group, and generated-pair
    carriers are the exact ones from the R-1164 model imported above. -/
def claim31732 : Prop :=
  r1164RetainedCount = 50262 ∧
    ∀ r : R1164RetainedRow,
      r1164DisplayedTransporter r rankFiveZero = rankFiveZero

end MathlibPlus.Open.ResearchFormalization.R1164
