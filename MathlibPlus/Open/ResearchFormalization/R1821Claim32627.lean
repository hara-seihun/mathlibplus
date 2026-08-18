import MathlibPlus.Open.ResearchFormalization.R1821Claim32626

namespace MathlibPlus.Open.ResearchFormalization.R1821Claim32627

noncomputable section

open MathlibPlus.Open.ResearchBatch.ActualAffine
open MathlibPlus.Open.ResearchFormalization.R1821Suborbits
open MathlibPlus.Open.ResearchFormalization.PermutationClaims

/-- Conjugacy of the classified copy with the natural translation copy, using
    the displayed quadratic transporter and requiring that transporter to lie
    in the generated ordered two-closure. -/
def conjugacyInGeneratedTwoClosure (B : Matrix (Fin 5) (Fin 5) F3) : Prop :=
  quadraticTransporter B ∈ twoClosure (generatedGroup B) ∧
    ∀ u : Equiv.Perm Omega3,
      u ∈ quadraticCopy B ↔
        ∃ v : Equiv.Perm Omega3,
          v ∈ translationImageGroup ∧
            u = (quadraticTransporter B)⁻¹ * v * quadraticTransporter B

/-- Claim 32627: every symmetric-matrix copy in the complete actual-image
    family is conjugate to the natural translation copy inside its generated
    two-closure by its displayed quadratic transporter. -/
def closureConjugacyAllClassifiedCopies_claim32627 : Prop :=
  ∀ B : Matrix (Fin 5) (Fin 5) F3,
    B.IsSymm → conjugacyInGeneratedTwoClosure B

end

end MathlibPlus.Open.ResearchFormalization.R1821Claim32627
