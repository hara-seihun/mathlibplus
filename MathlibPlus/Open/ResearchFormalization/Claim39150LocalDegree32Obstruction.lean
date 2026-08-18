import MathlibPlus.Open.ResearchFormalization.Batch39139
import MathlibPlus.Open.Research.R1549Displacement39143

namespace MathlibPlus.Open.ResearchFormalization.Claim39150LocalDegree32Obstruction

noncomputable section

open MathlibPlus.Open.ResearchFormalization.Batch39139
open MathlibPlus.Open.Research.R1549Displacement39143

/-- Claim 39150: every literal regular affine-`E32` pair is conjugate inside
its finest symmetric unordered-binary orbital closure, and the same exact
conjugator can be chosen with a proper displacement span and pointwise-trivial
action on the resulting nontrivial binary quotient. -/
def claim39150 : Prop :=
  Batch39139.claim39139 ∧
    Batch39139.claim39142 ∧
    MathlibPlus.Open.Research.R1549Displacement39143.claim39143

end

end MathlibPlus.Open.ResearchFormalization.Claim39150LocalDegree32Obstruction
