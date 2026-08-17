import Mathlib
import MathlibPlus.Open.ResearchFormalization.Batch1484

namespace MathlibPlus.Open.ResearchFormalization.R1710Claim33543

noncomputable section

abbrev F7 := ZMod 7
abbrev H := MathlibPlus.Open.ResearchFormalization.Batch1484.H
abbrev W := MathlibPlus.Open.ResearchFormalization.Batch1484.W 2
abbrev GLW := W ≃ₗ[F7] W
abbrev Carrier := W × H

open MathlibPlus.Open.ResearchFormalization.Batch1484

def hInverse (h : H) : H :=
  (-((2 : F7) ^ ((3 - h.2.val) % 3)) * h.1, -h.2)

def normalizedAffineProfile (L : H → GLW) (τ : H → W) : Prop :=
  L hOne = LinearEquiv.refl F7 W ∧ τ hOne = 0

def affineProfile (L : H → GLW) (τ : H → W)
    (x : Carrier) : Carrier :=
  (L x.2 x.1 + τ x.2, x.2)

def groupMul (x y : Carrier) : Carrier :=
  (x.1 + matchingScalarCharacter x.2 • y.1, hMul x.2 y.2)

def groupInverse (x : Carrier) : Carrier :=
  (-((matchingScalarCharacter x.2)⁻¹) • x.1, hInverse x.2)

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
    α (0, hOne) = (0, hOne) ∧
      ∀ x y : Carrier,
        α (groupMul x y) = groupMul (α x) (α y)

def orbitImageShadow (L : H → GLW) (τ z : H → W) : Prop :=
  globalCocycle z ∧
    profileGroupAutomorphism (cocycleAutomorphism z) ∧
      ∀ s : Carrier,
        Set.image (cocycleAutomorphism z) (exactDerivativeOrbit L τ s) =
          Set.image (affineProfile L τ) (exactDerivativeOrbit L τ s)

def hostileMatrix : Matrix (Fin 2) (Fin 2) F7 :=
  fun i j =>
    if i = 0 ∧ j = 0 then 0 else
      if i = 0 ∧ j = 1 then 1 else
        if i = 1 ∧ j = 0 then 6 else 3

def hostileMatrixAction (x : W) : W :=
  hostileMatrix.mulVec x

def invariantLine (U : Submodule F7 W) : Prop :=
  U ≠ ⊥ ∧
    Module.finrank F7 U = 1 ∧
      ∀ x : W, x ∈ U → hostileMatrixAction x ∈ U

def splitMonomial (M : Matrix (Fin 2) (Fin 2) F7) : Prop :=
  (∀ i : Fin 2, ∃! j : Fin 2, M i j ≠ 0) ∧
    (∀ j : Fin 2, ∃! i : Fin 2, M i j ≠ 0)

def splitMonomialNormalizer : Set (Matrix (Fin 2) (Fin 2) F7) :=
  {M | splitMonomial M}

def hostileMatrixFacts : Prop :=
  hostileMatrix ^ 8 = (1 : Matrix (Fin 2) (Fin 2) F7) ∧
    (∀ n : ℕ, 0 < n → n < 8 →
      hostileMatrix ^ n ≠ (1 : Matrix (Fin 2) (Fin 2) F7)) ∧
    (¬ ∃ U : Submodule F7 W, invariantLine U) ∧
    splitMonomialNormalizer.ncard = 72 ∧
      hostileMatrix ∉ splitMonomialNormalizer

def onePointMultiplier (q : H) (A : GLW) : H → GLW :=
  fun h => if h = q then A else LinearEquiv.refl F7 W

def zeroTranslation : H → W :=
  fun _ => 0

def hostileMatrixRealization (A : GLW) : Prop :=
  ∀ x : W, A x = hostileMatrixAction x

def derivativeDefect (L : H → GLW) (τ : H → W)
    (h k : H) : W :=
  (L h).symm
    (τ (hMul h k) - τ h - matchingScalarCharacter h • τ k)

def basepointTranslation (L : H → GLW) (h k : H) (x : W) : W :=
  (L h).symm
    (matchingScalarCharacter h •
      (L (hMul h k) x - L k x))

def derivativeTranslationCore (L : H → GLW) (τ : H → W)
    (h : H) : Submodule F7 W :=
  Submodule.span F7
    (Set.range (fun k : H => derivativeDefect L τ h k) ∪
      Set.range (fun kx : H × W =>
        basepointTranslation L h kx.1 kx.2))

def hostileProfileHistogram (q : H) (A : GLW) : Prop :=
  let L := onePointMultiplier q A
  let τ := zeroTranslation
  (Set.ncard {h : H | derivativeTranslationCore L τ h = ⊥} = 1) ∧
    (Set.ncard {h : H | derivativeTranslationCore L τ h = ⊤} = 20) ∧
    (∀ h : H,
      derivativeTranslationCore L τ h = ⊥ ∨
        derivativeTranslationCore L τ h = ⊤) ∧
    (Set.ncard {h : H |
      Nat.card (derivativeTranslationCore L τ h : Type) = 1} = 1) ∧
    (Set.ncard {h : H |
      Nat.card (derivativeTranslationCore L τ h : Type) = 49} = 20)

def globalCocycles : Set (H → W) :=
  {z | globalCocycle z}

def exactShadowForHostileProfile (q : H) (A : GLW)
    (z : H → W) : Prop :=
  orbitImageShadow (onePointMultiplier q A) zeroTranslation z

def claim33543 : Prop :=
  hostileMatrixFacts ∧
    ∃ q : H, q ≠ hOne ∧
      ∃ A : GLW,
        hostileMatrixRealization A ∧
          normalizedAffineProfile (onePointMultiplier q A) zeroTranslation ∧
          hostileProfileHistogram q A ∧
          globalCocycles.ncard = 2401 ∧
          ∀ z : H → W, z ∈ globalCocycles →
            exactShadowForHostileProfile q A z

end

end MathlibPlus.Open.ResearchFormalization.R1710Claim33543
