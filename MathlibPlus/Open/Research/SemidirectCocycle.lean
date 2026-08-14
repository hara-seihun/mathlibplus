import Mathlib

noncomputable section

namespace MathlibPlus.Open.Research.SemidirectCocycle

abbrev ShadowGroup := ZMod 13 × ZMod 3
abbrev ShadowModule := ZMod 7 × ZMod 7

def shadowIdentity : ShadowGroup := (0, 0)

def shadowMul (x y : ShadowGroup) : ShadowGroup :=
  (x.1 + (3 : ZMod 13) ^ (x.2.val) * y.1, x.2 + y.2)

def shadowInverse (x : ShadowGroup) : ShadowGroup :=
  (-((3 : ZMod 13) ^ (3 - x.2.val) * x.1), -x.2)

def shadowCharacter (x : ShadowGroup) : ZMod 7 :=
  (2 : ZMod 7) ^ x.2.val

def claim42495 : Prop :=
  (Fintype.card ShadowGroup = 39) ∧
    (Module.finrank (ZMod 7) ShadowModule = 2) ∧
    ((3 : ZMod 13) ^ 3 = 1) ∧
    ((2 : ZMod 7) ^ 3 = 1) ∧
    (∀ x y z : ShadowGroup,
      shadowMul (shadowMul x y) z = shadowMul x (shadowMul y z)) ∧
    (∀ x : ShadowGroup,
      shadowMul shadowIdentity x = x ∧ shadowMul x shadowIdentity = x) ∧
    (∀ x : ShadowGroup,
      shadowMul x (shadowInverse x) = shadowIdentity ∧
        shadowMul (shadowInverse x) x = shadowIdentity) ∧
    (∀ x y : ShadowGroup,
      shadowCharacter (shadowMul x y) = shadowCharacter x * shadowCharacter y)

def twistedDefect (τ : ShadowGroup → ShadowModule)
    (h k : ShadowGroup) : ShadowModule :=
  τ (shadowMul h k) - τ h - shadowCharacter h • τ k

def twistedDefectRank (τ : ShadowGroup → ShadowModule) (h : ShadowGroup) : ℕ :=
  Module.finrank (ZMod 7)
    (Submodule.span (ZMod 7) (Set.range (fun k => twistedDefect τ h k)))

def claim42496 : Prop :=
  ∀ (τ : ShadowGroup → ShadowModule),
    τ shadowIdentity = 0 →
      (∀ h : ShadowGroup,
        twistedDefectRank τ h ∈ ({0, 1, 2} : Set ℕ)) ∧
      ((∀ h k : ShadowGroup, twistedDefect τ h k = 0) →
        ∀ h : ShadowGroup, twistedDefectRank τ h = 0)

end MathlibPlus.Open.Research.SemidirectCocycle
