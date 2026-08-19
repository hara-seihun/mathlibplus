import MathlibPlus.Open.ResearchFormalization.R0667Claim29491

namespace MathlibPlus.Open.ResearchFormalization.R0667Claim29489

open MathlibPlus.Open.ResearchFormalization.R0667Claim29491

noncomputable section

/-- Claim 29489: the exact map-bearing predicate for a complete root-origin
incidence certificate.  The certificate is an input to this predicate; no
existence assertion is made for arbitrary graphs or masks. -/
def completeIncidenceCertificate_claim29489
    {B P K : Type*}
    [Fintype B] [DecidableEq B]
    [Fintype P] [DecidableEq P]
    [Fintype K] [DecidableEq K]
    (m : ℕ)
    (F : SimpleGraph B) (Pgraph : SimpleGraph P) (Kgraph : SimpleGraph K)
    (S : Set B)
    (c : CompleteIncidenceData F Pgraph Kgraph S) : Prop :=
  Fintype.card B = m ∧
    Fintype.card P = m ∧
    Fintype.card K = m - 1 ∧
    completeIncidenceValid F Pgraph Kgraph S c

end

end MathlibPlus.Open.ResearchFormalization.R0667Claim29489
