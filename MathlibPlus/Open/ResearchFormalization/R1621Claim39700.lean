import MathlibPlus.Open.Geometry.HeisenbergBorel39693_39697

namespace MathlibPlus.Open.ResearchFormalization.R1621Claim39700

open MathlibPlus.Open.Geometry.HeisenbergBorel39693_39697

noncomputable section

abbrev SubgroupOfAffineBorel7 :=
  {Γ : Subgroup Perm7 // Γ ≤ affineBorel7}

def subgroupConjugate7 (Γ Δ : SubgroupOfAffineBorel7) : Prop :=
  ∃ g : affineBorel7, ∀ h : Perm7,
    h ∈ Γ.1 ↔ (g : Perm7) * h * (g : Perm7)⁻¹ ∈ Δ.1

def linearImageSet7 (K : Subgroup Perm7) : Set linearBorel7 :=
  {b | ∃ g : K, ∃ t : W7,
    ∀ z : W7, (g : Perm7) z = t + (b : Perm7) z}

def linearImageOrder7 (K : Subgroup Perm7) : ℕ :=
  Nat.card {b : linearBorel7 // b ∈ linearImageSet7 K}

def exceptionalExcess7 (Γ : SubgroupOfAffineBorel7) : Prop :=
  strictlyContains7 (translationCore7 Γ.1) (translationStabilizer7 Γ.1)

def exceptionalOrderPair7 (Γ : SubgroupOfAffineBorel7) : Prop :=
  (Nat.card Γ.1 = 49 ∧ linearImageOrder7 Γ.1 = 7) ∨
    (Nat.card Γ.1 = 98 ∧ linearImageOrder7 Γ.1 = 14) ∨
      (Nat.card Γ.1 = 147 ∧ linearImageOrder7 Γ.1 = 21) ∨
        (Nat.card Γ.1 = 294 ∧ linearImageOrder7 Γ.1 = 42)

def exceptionalCoreShape7 (Γ : SubgroupOfAffineBorel7) : Prop :=
  Nat.card (heisenbergCore7 Γ.1) = 49 ∧
    transitive7 (heisenbergCore7 Γ.1) ∧
      translationCore7 (heisenbergCore7 Γ.1) = flagVectors7 ∧
        translationCore7 Γ.1 = flagVectors7 ∧
          translationStabilizer7 Γ.1 = (Set.univ : Set W7)

def exceptionalClassRepresentatives7
    (R : Set SubgroupOfAffineBorel7) : Prop :=
  Nat.card R = 4 ∧
    (∀ Γ : SubgroupOfAffineBorel7,
      Γ ∈ R → exceptionalExcess7 Γ) ∧
      (∀ Γ : SubgroupOfAffineBorel7,
        exceptionalExcess7 Γ ↔
          ∃ Δ : SubgroupOfAffineBorel7,
            Δ ∈ R ∧ subgroupConjugate7 Γ Δ) ∧
        (∀ Γ Δ : SubgroupOfAffineBorel7,
          Γ ∈ R → Δ ∈ R → subgroupConjugate7 Γ Δ → Γ = Δ)

def exceptionalOrderPairsOccur7 : Prop :=
  (∃ Γ : SubgroupOfAffineBorel7,
    exceptionalExcess7 Γ ∧ Nat.card Γ.1 = 49 ∧
      linearImageOrder7 Γ.1 = 7) ∧
    (∃ Γ : SubgroupOfAffineBorel7,
      exceptionalExcess7 Γ ∧ Nat.card Γ.1 = 98 ∧
        linearImageOrder7 Γ.1 = 14) ∧
      (∃ Γ : SubgroupOfAffineBorel7,
        exceptionalExcess7 Γ ∧ Nat.card Γ.1 = 147 ∧
          linearImageOrder7 Γ.1 = 21) ∧
        (∃ Γ : SubgroupOfAffineBorel7,
          exceptionalExcess7 Γ ∧ Nat.card Γ.1 = 294 ∧
            linearImageOrder7 Γ.1 = 42)

/-- Claim 39700: exactly the four exceptional classes and 132 literal
subgroups, with both the exact paired orders and the complete core shape. -/
def claim39700_exactExceptionalClassCensus : Prop :=
  Nat.card {Γ : SubgroupOfAffineBorel7 // exceptionalExcess7 Γ} = 132 ∧
    (∃ R : Set SubgroupOfAffineBorel7,
      exceptionalClassRepresentatives7 R) ∧
      (∀ Γ : SubgroupOfAffineBorel7,
        exceptionalExcess7 Γ →
          exceptionalOrderPair7 Γ ∧ exceptionalCoreShape7 Γ) ∧
        exceptionalOrderPairsOccur7

end

end MathlibPlus.Open.ResearchFormalization.R1621Claim39700
