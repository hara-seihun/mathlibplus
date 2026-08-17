import Mathlib
import MathlibPlus.Open.ResearchFormalization.R1210SmallProfiles

namespace MathlibPlus.Open.ResearchFormalization.R1210Claim42048

open scoped BigOperators
noncomputable section

open MathlibPlus.Open.ResearchFormalization.C7AffineSectionTransporter
open MathlibPlus.Open.ResearchFormalization.R1210SmallProfiles

private abbrev A7 := Fin 2 → ZMod 7

private def developmentAdj (B : Finset A7) (p q : A7 × Bool) : Prop :=
  (p.2 = false ∧ q.2 = true ∧ q.1 - 2 • p.1 ∈ B) ∨
    (p.2 = true ∧ q.2 = false ∧ p.1 - 2 • q.1 ∈ B)

private def sideMap (psi0 psi1 : Equiv.Perm A7)
    (p : A7 × Bool) : A7 × Bool :=
  if p.2 then (psi1 p.1, true) else (psi0 p.1, false)

private def sidePreservingDevelopmentIso
    (B C : Finset A7) (psi0 psi1 : Equiv.Perm A7) : Prop :=
  ∀ p q,
    developmentAdj B p q ↔
      developmentAdj C (sideMap psi0 psi1 p) (sideMap psi0 psi1 q)

private def developmentEquivalent (B C : Finset A7) : Prop :=
  ∃ psi0 psi1 : Equiv.Perm A7,
    sidePreservingDevelopmentIso B C psi0 psi1

private def affineEquivalent (B C : Finset A7) : Prop :=
  ∃ L : A7 ≃ₗ[ZMod 7] A7, ∃ c : A7,
    C = MathlibPlus.Open.ResearchFormalization.C7AffineSectionTransporter.affineImage
      L c B

private def subsetComplement (B : Finset A7) : Finset A7 :=
  Finset.univ \ B

private def affineDevelopmentRigidity (k : ℕ) : Prop :=
  ∀ B C : Finset A7,
    B.card = k → C.card = k →
      developmentEquivalent B C → affineEquivalent B C

private def profileCIHarmlessAt (k : ℕ) : Prop :=
  ∀ (K B C : Finset A7)
    (psi : Fin 3 → A7 → A7),
    normalizedProfile K B C psi →
    B.card = k →
    ∃ (L : A7 ≃ₗ[ZMod 7] A7) (c : A7),
      C = MathlibPlus.Open.ResearchFormalization.C7AffineSectionTransporter.affineImage
        L c B ∧
      extensionAutomorphism (sectionTransport L c) ∧
      (profileConnectionSet K B).image (sectionTransport L c) =
        profileConnectionSet K C

/-- Complement transfer for the two-sided development and the affine section. -/
def bipartiteComplementation_claim42048 : Prop :=
  Fintype.card A7 = 49 ∧
  (∀ B C : Finset A7,
    developmentEquivalent B C ↔
      developmentEquivalent (subsetComplement B) (subsetComplement C)) ∧
  (∀ B C : Finset A7,
    affineEquivalent B C ↔
      affineEquivalent (subsetComplement B) (subsetComplement C)) ∧
  (∀ k : ℕ, k ≤ 49 →
    affineDevelopmentRigidity k →
      affineDevelopmentRigidity (49 - k)) ∧
  (∀ k : ℕ, k ≤ 49 →
    profileCIHarmlessAt k →
      profileCIHarmlessAt (49 - k))

end
end MathlibPlus.Open.ResearchFormalization.R1210Claim42048
