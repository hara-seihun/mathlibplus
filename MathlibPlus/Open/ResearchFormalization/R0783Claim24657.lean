import MathlibPlus.Open.ResearchFormalization.R0783.Claims24662_24663
import MathlibPlus.Open.ResearchFormalization.PrimePowerDivisibilityClaim24656

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0783Claim24657

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R0783
open MathlibPlus.Open.ResearchFormalization.PrimePowerDivisibilityClaim24656

/-- Claim 24657: the exact divided collar coefficient reduces in the selected
prime quotient to the outside residue times the elementary attachment-cavity
statistic, with the actual tree-closure and repeated-child carriers retained. -/
def claim24657 : Prop :=
  ∀ {n e : ℕ} (p L : CavityRing n)
    (B : Fin e → LowerCavityRing n)
    (Q : Fin e → Polynomial (CavityRing n))
    (H P : Polynomial (CavityRing n)),
    primePowerCollarSetup p L
      (fun a => lowerCavityEmbedding n (B a)) Q H P →
      ∀ k : ℕ, 0 ≤ k → k ≤ e →
        ∃ q : CavityRing n,
          P.coeff k = p ^ (e - k) * q ∧
            Ideal.Quotient.mk (Ideal.span ({p} : Set (CavityRing n))) q =
              Ideal.Quotient.mk (Ideal.span ({p} : Set (CavityRing n))) L *
                Ideal.Quotient.mk (Ideal.span ({p} : Set (CavityRing n)))
                  (elementaryCavity
                    (fun a => lowerCavityEmbedding n (B a)) k)

end

end MathlibPlus.Open.ResearchFormalization.R0783Claim24657
