import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1210Claim42045

open scoped BigOperators

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

private def affineImage (L : A7 ≃ₗ[ZMod 7] A7) (c : A7)
    (B : Finset A7) : Finset A7 :=
  B.image (fun x => L x + c)

private def affineEquivalent (B C : Finset A7) : Prop :=
  ∃ L : A7 ≃ₗ[ZMod 7] A7, ∃ c : A7, C = affineImage L c B

/-- Claim 42045: through weight thirteen, a side-preserving isomorphism of
 the exact 98-vertex translation developments forces affine equivalence. -/
def affineDevelopmentRigidityThroughThirteen_claim42045 : Prop :=
  Fintype.card (A7 × Bool) = 98 ∧
    ∀ (B C : Finset A7),
      B.card = C.card →
        B.card ≤ 13 →
          developmentEquivalent B C → affineEquivalent B C

end MathlibPlus.Open.ResearchFormalization.R1210Claim42045
