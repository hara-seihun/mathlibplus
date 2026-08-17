import MathlibPlus.Open.ResearchFormalization.R1210SmallProfiles

namespace MathlibPlus.Open.ResearchFormalization.R1210WeightTheorem

open MathlibPlus.Open.ResearchFormalization.C7AffineSectionTransporter
open MathlibPlus.Open.ResearchFormalization.R1210SmallProfiles

noncomputable section

abbrev A7 := C7Vector

def translated (B : Finset A7) (t : A7) : Finset A7 :=
  B.image (fun b => b + t)

def developmentAdj (B : Finset A7) (p q : A7 × Bool) : Prop :=
  (p.2 = false ∧ q.2 = true ∧ q.1 - 2 • p.1 ∈ B) ∨
    (p.2 = true ∧ q.2 = false ∧ p.1 - 2 • q.1 ∈ B)

def sideMap (ψ₀ ψ₁ : Equiv.Perm A7) (p : A7 × Bool) : A7 × Bool :=
  if p.2 then (ψ₁ p.1, true) else (ψ₀ p.1, false)

def sidePreservingDevelopmentIso
    (B C : Finset A7) (ψ₀ ψ₁ : Equiv.Perm A7) : Prop :=
  ∀ p q,
    developmentAdj B p q ↔
      developmentAdj C (sideMap ψ₀ ψ₁ p) (sideMap ψ₀ ψ₁ q)

def developmentEquivalent (B C : Finset A7) : Prop :=
  ∃ ψ₀ ψ₁ : Equiv.Perm A7,
    sidePreservingDevelopmentIso B C ψ₀ ψ₁

def affineEquivalent (B C : Finset A7) : Prop :=
  ∃ L : A7 ≃ₗ[ZMod 7] A7, ∃ c : A7, C = affineImage L c B

def weightedSubset (k : ℕ) := {B : Finset A7 // B.card = k}

def affineWeightedRel (k : ℕ)
    (B C : weightedSubset k) : Prop := affineEquivalent B.1 C.1
abbrev affineType (k : ℕ) := Quot (affineWeightedRel k)

def developmentWeightedRel (k : ℕ)
    (B C : weightedSubset k) : Prop := developmentEquivalent B.1 C.1
abbrev developmentType (k : ℕ) := Quot (developmentWeightedRel k)

noncomputable def subsetCount (k : ℕ) : ℕ :=
  Nat.card (weightedSubset k)

noncomputable def affineOrbitCount (k : ℕ) : ℕ :=
  Nat.card (affineType k)

noncomputable def developmentTypeCount (k : ℕ) : ℕ :=
  Nat.card (developmentType k)

def developmentCollisionType (k : ℕ) (q : developmentType k) : Prop :=
  ∃ B C : weightedSubset k,
    Quot.mk (developmentWeightedRel k) B = q ∧
      Quot.mk (developmentWeightedRel k) C = q ∧
        ¬ affineEquivalent B.1 C.1

noncomputable def developmentCollisionCount (k : ℕ) : ℕ :=
  Nat.card {q : developmentType k // developmentCollisionType k q}

def exactAtlasRow (k subsets classes collisions : ℕ) : Prop :=
  subsetCount k = subsets ∧
    affineOrbitCount k = classes ∧
      developmentTypeCount k = classes ∧
        developmentCollisionCount k = collisions

def profileHarmlessAtPair (small large : ℕ) : Prop :=
  ∀ (K B C : Finset A7)
    (ψ : Fin 3 → A7 → A7),
    normalizedProfile K B C ψ →
      (B.card = small ∨ B.card = large) →
        ∃ (L : A7 ≃ₗ[ZMod 7] A7) (c : A7),
          C = affineImage L c B ∧
            extensionAutomorphism (sectionTransport L c) ∧
            (profileConnectionSet K B).image (sectionTransport L c) =
              profileConnectionSet K C

def exactWeightTheorems_claim32280 : Prop :=
  (profileHarmlessAtPair 8 41 ∧
    profileHarmlessAtPair 9 40 ∧
    profileHarmlessAtPair 10 39 ∧
    profileHarmlessAtPair 11 38 ∧
    profileHarmlessAtPair 12 37 ∧
    profileHarmlessAtPair 13 36) ∧
  (exactAtlasRow 8 450978066 4758 0 ∧
    exactAtlasRow 9 2054455634 21225 0 ∧
    exactAtlasRow 10 8217822536 84050 0 ∧
    exactAtlasRow 11 29135916264 296557 0 ∧
    exactAtlasRow 12 92263734836 937022 0 ∧
    exactAtlasRow 13 262596783764 2663422 0)

end
end MathlibPlus.Open.ResearchFormalization.R1210WeightTheorem
