import MathlibPlus.Open.Research.CIAtlas
import MathlibPlus.Open.ResearchFormalization.R0980PartitionSplit27860

namespace MathlibPlus.Open.ResearchFormalization.R0980Claim27859

open MathlibPlus.Open.Research.CIAtlas
open MathlibPlus.Open.ResearchFormalization.R0980PartitionSplit27860

noncomputable section

/-- The complete valency-thirteen graph/presentation atlas, together with the
normal and nonnormal presentation census, has the admitted 30,638/4,384
split. -/
def normalAndNonnormalPresentationCensus_claim27859 : Prop :=
  claim27854 ∧
    presentationCensus 30638
      (fun S => normalPresentation S.1) ∧
    presentationCensus 4384
      (fun S => ¬ normalPresentation S.1) ∧
    30638 + 4384 = 35022 ∧
    (∀ S : Presentation13,
      normalPresentation S.1 ∨ ¬ normalPresentation S.1)

end

end MathlibPlus.Open.ResearchFormalization.R0980Claim27859
