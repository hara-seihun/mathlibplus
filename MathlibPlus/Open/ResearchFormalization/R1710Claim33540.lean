import Mathlib
import MathlibPlus.Open.ResearchFormalization.R1710Claim33538
import MathlibPlus.Open.ResearchFormalization.R1710Claim33539

namespace MathlibPlus.Open.ResearchFormalization.R1710Claim33540

noncomputable section

abbrev F7 := ZMod 7
abbrev H := MathlibPlus.Open.ResearchFormalization.Batch1484.H
abbrev W := MathlibPlus.Open.ResearchFormalization.Batch1484.W 2
abbrev GLW := W ≃ₗ[F7] W
abbrev Carrier := W × H

open MathlibPlus.Open.ResearchFormalization.Batch1484

abbrev hInverse :=
  MathlibPlus.Open.ResearchFormalization.R1710Claim33538.hInverse

abbrev normalizedAffineProfile :=
  MathlibPlus.Open.ResearchFormalization.R1710Claim33538.normalizedAffineProfile

def multiplierImage (L : H → GLW) : Subgroup GLW :=
  Subgroup.closure (Set.range L)

def affineProfile (L : H → GLW) (τ : H → W)
    (x : Carrier) : Carrier :=
  (L x.2 x.1 + τ x.2, x.2)

def groupMul (x y : Carrier) : Carrier :=
  (x.1 + matchingScalarCharacter x.2 • y.1, hMul x.2 y.2)

def groupInverse (x : Carrier) : Carrier :=
  (-((matchingScalarCharacter x.2)⁻¹) • x.1, hInverse x.2)

def groupOne : Carrier :=
  (0, hOne)

def profileInverse (L : H → GLW) (τ : H → W)
    (x : Carrier) : Carrier :=
  ((L x.2).symm (x.1 - τ x.2), x.2)

def normalizedRelativeDerivative (L : H → GLW) (τ : H → W)
    (x s : Carrier) : Carrier :=
  profileInverse L τ
    (groupMul
      (groupInverse (affineProfile L τ x))
      (affineProfile L τ (groupMul x s)))

def derivativeStepRelation (L : H → GLW) (τ : H → W)
    (s t : Carrier) : Prop :=
  ∃ x : Carrier, normalizedRelativeDerivative L τ x s = t

def exactDerivativeOrbit (L : H → GLW) (τ : H → W)
    (s : Carrier) : Set Carrier :=
  {t | Relation.EqvGen (derivativeStepRelation L τ) s t}

def cocycleAutomorphism (z : H → W) (x : Carrier) : Carrier :=
  (x.1 + z x.2, x.2)

def globalCocycle (z : H → W) : Prop :=
  ∀ h k : H,
    z (hMul h k) = z h + matchingScalarCharacter h • z k

def profileGroupAutomorphism (α : Carrier → Carrier) : Prop :=
  Function.Bijective α ∧
    α groupOne = groupOne ∧
      ∀ x y : Carrier,
        α (groupMul x y) = groupMul (α x) (α y)

def cocycleAutomorphismLaw (z : H → W) : Prop :=
  profileGroupAutomorphism (cocycleAutomorphism z)

def orbitImageShadow (L : H → GLW) (τ z : H → W) : Prop :=
  globalCocycle z ∧ cocycleAutomorphismLaw z ∧
    ∀ s : Carrier,
      Set.image (cocycleAutomorphism z) (exactDerivativeOrbit L τ s) =
        Set.image (affineProfile L τ) (exactDerivativeOrbit L τ s)

def identityFreeConnection (S : Set Carrier) : Prop :=
  groupOne ∉ S

def inverseClosedConnection (S : Set Carrier) : Prop :=
  ∀ x : Carrier, x ∈ S ↔ groupInverse x ∈ S

def cayleyRelation (S : Set Carrier) (x y : Carrier) : Prop :=
  x ≠ y ∧ groupMul (groupInverse x) y ∈ S

def directedCayleyTransport (f : Carrier → Carrier)
    (S T : Set Carrier) : Prop :=
  ∀ x y : Carrier,
    cayleyRelation S x y ↔ cayleyRelation T (f x) (f y)

def ciHarmlessVia (L : H → GLW) (τ z : H → W) : Prop :=
  ∀ S T : Set Carrier,
    identityFreeConnection S → inverseClosedConnection S →
      identityFreeConnection T → inverseClosedConnection T →
        directedCayleyTransport (affineProfile L τ) S T →
          Set.image (cocycleAutomorphism z) S = T

def dciHarmlessVia (L : H → GLW) (τ z : H → W) : Prop :=
  ∀ S T : Set Carrier,
    identityFreeConnection S → identityFreeConnection T →
      directedCayleyTransport (affineProfile L τ) S T →
        Set.image (cocycleAutomorphism z) S = T

/-- Claim 33540: one global cocycle shadow has the exact derivative-orbit
image and the distinct directed and inverse-closed connection-set consequences.
-/
def claim33540 : Prop :=
  ∀ (L : H → GLW) (τ : H → W),
    normalizedAffineProfile L τ →
      ¬ 7 ∣ Nat.card (multiplierImage L : Type) →
        ∃ z : H → W,
          orbitImageShadow L τ z ∧
            ciHarmlessVia L τ z ∧ dciHarmlessVia L τ z

end

end MathlibPlus.Open.ResearchFormalization.R1710Claim33540
