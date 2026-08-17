import MathlibPlus.Open.ResearchFormalization.R0783.Claims24662_24663

namespace MathlibPlus.Open.ResearchFormalization.R0783

/-- The first `e+1` exposed residue layers recover every elementary
attachment-cavity statistic in the reviewed prime-adic collar carrier. -/
def elementaryAttachmentCavityRecovery_claim24661 : Prop :=
  ∀ {n e : ℕ} (p L : CavityRing n)
    (B C : Fin e → LowerCavityRing n)
    (Q Q' : Fin e → Polynomial (CavityRing n))
    (H H' P P' : Polynomial (CavityRing n)),
    collarContext p L
      (fun a => lowerCavityEmbedding n (B a))
      (fun a => lowerCavityEmbedding n (C a))
      Q Q' H H' P P' →
      exposedResiduesAgree (e := e) p P P' →
        ∀ k : ℕ, k ≤ e → elementaryCavity B k = elementaryCavity C k

end MathlibPlus.Open.ResearchFormalization.R0783
