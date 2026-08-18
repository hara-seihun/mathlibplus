import MathlibPlus.Open.R1081.KernelGraphClassification_15b65c14
import MathlibPlus.Open.ResearchFormalization.Batch_7e3f7a79_Claim41320

namespace MathlibPlus.Open.ResearchFormalization.R1148Claim31552

open MathlibPlus.Open.R1081
open MathlibPlus.Open.ResearchFormalization.Batch_7e3f7a79_Claim41320

noncomputable section

abbrev F7_31552 := ZMod 7
abbrev Plane7_31552 := F7_31552 × F7_31552

def connectionSet31552 (Q I : Set F7_31552) : Set Plane7_31552 :=
  {p | (∃ i : F7_31552, i ∈ I ∧ p = (0, i)) ∨
    (∃ q : F7_31552, q ∈ Q ∧ ∃ y : F7_31552, p = (q, y))}

def claim31552 : Prop :=
  Set.range graphRow41320 = listedGraphRows41320 ∧
    ∀ i : Fin 4,
      let Q := graphQ41320 i
      let I := graphI41320 i
      connectionSet31552 Q I = kernelConnectionSet Q I ∧
        relationIsomorphism (kernelAdj Q I) (lexicographicKernelAdj Q I)
          (Equiv.refl Plane7_31552)

end

end MathlibPlus.Open.ResearchFormalization.R1148Claim31552
