import MathlibPlus.Open.ResearchFormalization.R0783.Claims24662_24663

namespace MathlibPlus.Open.ResearchFormalization.PrimePowerDivisibilityClaim24656

open MathlibPlus.Open.ResearchFormalization.R0783

noncomputable section

/-- The repeated-child collar setup, with the common closure retaining its
reviewed tree-closure shape. -/
def primePowerCollarSetup {n e : ℕ} (p L : CavityRing n)
    (B : Fin e → CavityRing n)
    (Q : Fin e → Polynomial (CavityRing n))
    (H P : Polynomial (CavityRing n)) : Prop :=
  treeClosureShape p ∧ collarSetup p B Q H P L

/-- Claim 24656: every coefficient through the repeated-child layer `e` has
its exact prime-power factor; the exponent is the number of displayed child
factors not opened at degree `k`. -/
def primePowerDivisibility_claim24656 : Prop :=
  ∀ {n e : ℕ} (p L : CavityRing n)
    (B : Fin e → CavityRing n)
    (Q : Fin e → Polynomial (CavityRing n))
    (H P : Polynomial (CavityRing n)),
    primePowerCollarSetup p L B Q H P →
      ∀ k : ℕ, 0 ≤ k → k ≤ e →
        ∃ q : CavityRing n,
          P.coeff k = p ^ (e - k) * q

end
end MathlibPlus.Open.ResearchFormalization.PrimePowerDivisibilityClaim24656
