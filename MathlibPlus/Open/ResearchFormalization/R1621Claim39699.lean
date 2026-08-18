import MathlibPlus.Open.Geometry.HeisenbergBorel39693_39697

namespace MathlibPlus.Open.ResearchFormalization.R1621Claim39699

open MathlibPlus.Open.Geometry.HeisenbergBorel39693_39697

noncomputable section

abbrev SubgroupOfAffineBorel7 :=
  {Γ : Subgroup Perm7 // Γ ≤ affineBorel7}

def subgroupConjugate7 (Γ Δ : SubgroupOfAffineBorel7) : Prop :=
  ∃ g : affineBorel7, ∀ h : Perm7,
    h ∈ Γ.1 ↔ (g : Perm7) * h * (g : Perm7)⁻¹ ∈ Δ.1

def subgroupConjugacyRepresentatives7
    (R : Set SubgroupOfAffineBorel7) : Prop :=
  Nat.card R = 218 ∧
    (∀ Γ : SubgroupOfAffineBorel7,
      ∃ Δ : SubgroupOfAffineBorel7,
        Δ ∈ R ∧ subgroupConjugate7 Γ Δ) ∧
      (∀ Γ Δ : SubgroupOfAffineBorel7,
        Γ ∈ R → Δ ∈ R → subgroupConjugate7 Γ Δ → Γ = Δ)

/-- Claim 39699: the exact literal census, a complete set of conjugacy
representatives, and the stabilizer equality through the Heisenberg core. -/
def claim39699_completeSubgroupCensus : Prop :=
  Nat.card SubgroupOfAffineBorel7 = 12282 ∧
    (∃ R : Set SubgroupOfAffineBorel7,
      subgroupConjugacyRepresentatives7 R) ∧
      ∀ Γ : SubgroupOfAffineBorel7,
        translationStabilizer7 Γ.1 =
          translationStabilizer7 (heisenbergCore7 Γ.1)

end

end MathlibPlus.Open.ResearchFormalization.R1621Claim39699
