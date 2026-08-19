import MathlibPlus.Open.ResearchFormalization.R1148Claim41317
import MathlibPlus.Open.R1081.KernelGraphClassification_15b65c14
import MathlibPlus.Open.ResearchFormalization.Batch_7e3f7a79_Claim41320

namespace MathlibPlus.Open.ResearchFormalization.R1148KernelValencies

noncomputable section

open MathlibPlus.Open.R1081
open MathlibPlus.Open.ResearchFormalization.R1148Claim41317
open MathlibPlus.Open.ResearchFormalization.Batch_7e3f7a79_Claim41320

/-- Claims 31553 and 41318: the four exact R-1148 kernel graph rows have
valencies 14, 20, 28, and 34 at indices 49, 52, 2769, and 2772. -/
def exactFourKernelGraphValencies_claim31553_41318 : Prop :=
  (∀ i : Fin 4,
    (graphIndex41320 i,
      kernelValency (graphQ41320 i) (graphI41320 i)) =
      ![(49, 14), (52, 20), (2769, 28), (2772, 34)] i)

end

end MathlibPlus.Open.ResearchFormalization.R1148KernelValencies
