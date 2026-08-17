import Mathlib
import MathlibPlus.Open.ResearchFormalization.Batch1484

namespace MathlibPlus.Open.ResearchFormalization.R1710Claim33538

noncomputable section

abbrev F7 := ZMod 7
abbrev H := MathlibPlus.Open.ResearchFormalization.Batch1484.H
abbrev W := MathlibPlus.Open.ResearchFormalization.Batch1484.W 2
abbrev GLW := W ≃ₗ[F7] W

open MathlibPlus.Open.ResearchFormalization.Batch1484

def hInverse (h : H) : H :=
  (-((2 : F7) ^ ((3 - h.2.val) % 3)) * h.1, -h.2)

def normalizedAffineProfile (L : H → GLW) (τ : H → W) : Prop :=
  L hOne = LinearEquiv.refl F7 W ∧ τ hOne = 0

def qL (L : H → GLW) : Set H :=
  {h | ∀ k : H, L (hMul h k) = L k}

def aL (L : H → GLW) (τ : H → W) : Set H :=
  {h | h ∈ qL L ∧
    ∀ k : H, k ∈ qL L →
      τ (hMul h k) = τ h + matchingScalarCharacter h • τ k}

def aLSubgroup (L : H → GLW) (τ : H → W) : Prop :=
  hOne ∈ aL L τ ∧
    (∀ a b : H, a ∈ aL L τ → b ∈ aL L τ → hMul a b ∈ aL L τ) ∧
      (∀ a : H, a ∈ aL L τ → hInverse a ∈ aL L τ)

def restrictedCocycle (S : Set H) (z : H → W) : Prop :=
  ∀ h k : H, h ∈ S → k ∈ S →
    z (hMul h k) = z h + matchingScalarCharacter h • z k

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

def zeroCore (L : H → GLW) (τ : H → W) (h : H) : Prop :=
  derivativeTranslationCore L τ h = ⊥

def claim33538 : Prop :=
  ∀ (L : H → GLW) (τ : H → W),
    normalizedAffineProfile L τ →
      aLSubgroup L τ ∧
        (∀ h : H, zeroCore L τ h → h ∈ aL L τ) ∧
          restrictedCocycle (aL L τ) τ

end

end MathlibPlus.Open.ResearchFormalization.R1710Claim33538
