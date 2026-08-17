import MathlibPlus.Open.ResearchFormalization.R1821Suborbits

namespace MathlibPlus.Open.ResearchFormalization.R1821Claim32625

noncomputable section

open MathlibPlus.Open.ResearchBatch.ActualAffine
open MathlibPlus.Open.ResearchFormalization.R1821Suborbits

/-- Claim 32625: the quadratic transporter fixes every exact point-stabilizer
suborbit of the generated group setwise. -/
def quadraticTransporterFixesEveryPointStabilizerSuborbit_claim32625 : Prop :=
  ∀ B : Matrix (Fin 5) (Fin 5) F3, B.IsSymm →
    ∀ h : H3, ∀ z : F3,
      Set.image (quadraticTransporter B)
          (pointStabilizerOrbit (generatedGroup B) (z, h)) =
        pointStabilizerOrbit (generatedGroup B) (z, h)

end

end MathlibPlus.Open.ResearchFormalization.R1821Claim32625
