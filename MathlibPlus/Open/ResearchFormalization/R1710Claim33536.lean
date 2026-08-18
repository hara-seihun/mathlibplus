import Mathlib
import MathlibPlus.Open.ResearchFormalization.R1710Claim33538

namespace MathlibPlus.Open.ResearchFormalization.R1710Claim33536

noncomputable section

abbrev F7 := ZMod 7
abbrev H := MathlibPlus.Open.ResearchFormalization.Batch1484.H
abbrev W := MathlibPlus.Open.ResearchFormalization.Batch1484.W 2
abbrev GLW := W ≃ₗ[F7] W

open MathlibPlus.Open.ResearchFormalization.Batch1484
open MathlibPlus.Open.ResearchFormalization.R1710Claim33538

def multiplierImage (L : H → GLW) : Subgroup GLW :=
  Subgroup.closure (Set.range L)

def invariantSubmodule (K : Subgroup GLW) (V : Submodule F7 W) : Prop :=
  ∀ g : K, ∀ x : W, x ∈ V → (g : GLW) x ∈ V

def irreducibleAction (K : Subgroup GLW) : Prop :=
  ∀ V : Submodule F7 W,
    invariantSubmodule K V → V = ⊥ ∨ V = ⊤

def multiplierDifferenceImage (L : H → GLW) (h : H) : Submodule F7 W :=
  Submodule.span F7 (Set.range (fun x : W => L h x - x))

def basepointVariationFormula (L : H → GLW) (h k : H) (x : W) : Prop :=
  basepointTranslation L h k x =
    (L h).symm
      (matchingScalarCharacter h •
        (L (hMul h k) x - L k x))

def claim_33536 : Prop :=
  ∀ (L : H → GLW) (τ : H → W),
    normalizedAffineProfile L τ →
      let K := multiplierImage L
      (∀ h : H,
        invariantSubmodule K (derivativeTranslationCore L τ h)) ∧
        (∀ h k : H, ∀ x : W,
          basepointVariationFormula L h k x) ∧
        (∀ h : H,
          multiplierDifferenceImage L h ≤
            derivativeTranslationCore L τ h) ∧
        (irreducibleAction K →
          (∀ h : H,
            derivativeTranslationCore L τ h = ⊥ ∨
              derivativeTranslationCore L τ h = ⊤) ∧
          (∀ h : H,
            derivativeTranslationCore L τ h = ⊥ →
              L h = LinearEquiv.refl F7 W))

end

end MathlibPlus.Open.ResearchFormalization.R1710Claim33536
