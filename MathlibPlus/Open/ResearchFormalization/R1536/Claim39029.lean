import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R1536

abbrev ShadowA := ZMod 5
abbrev ShadowD := ZMod 2 × ZMod 2
abbrev ShadowG := ShadowA × ShadowD

/-- The two distinct internal `V₄` elements used by the witness. -/
def shadowDOne : ShadowD := (0, 0)
def shadowDTwo : ShadowD := (1, 0)

def shadowSection (S : Set ShadowG) (a : ShadowA) : Set ShadowD :=
  {v | (a, v) ∈ S}

def shadowWeight (S : Set ShadowG) (a : ShadowA) : ℕ :=
  (shadowSection S a).ncard

def shadowConnectionSet (d₁ d₂ : ShadowD) : Set ShadowG :=
  {x | ((x.1 = 1 ∨ x.1 = -1) ∧ x.2 = d₁) ∨
    ((x.1 = 2 ∨ x.1 = -2) ∧ x.2 = d₂)}

def shadowAlpha (a : ShadowA) : ShadowA := 2 * a

def shadowLiftAlpha (x : ShadowG) : ShadowG :=
  (shadowAlpha x.1, x.2)

def shadowAdditiveAutomorphism (α : ShadowA → ShadowA) : Prop :=
  Function.Bijective α ∧ α 0 = 0 ∧
    ∀ a b : ShadowA, α (a + b) = α a + α b

def shadowIdentityFree (S : Set ShadowG) : Prop :=
  (0, 0) ∉ S

def shadowInverseClosed (S : Set ShadowG) : Prop :=
  ∀ x : ShadowG, x ∈ S ↔ -x ∈ S

def shadowFiveColorWeightShadow
    (S : Set ShadowG) (α : ShadowA → ShadowA) : Prop :=
  shadowIdentityFree S ∧
    shadowInverseClosed S ∧
    (∀ a : ShadowA, shadowWeight S a < 5) ∧
    shadowWeight S 0 = 0 ∧
    (∀ a : ShadowA, a ≠ 0 → shadowWeight S a = 1) ∧
    (∀ a : ShadowA, shadowWeight S (-a) = shadowWeight S a) ∧
    shadowAdditiveAutomorphism α ∧
    (∀ a : ShadowA, shadowWeight S (α a) = shadowWeight S a)

def shadowNaturalTranslation (g x : ShadowG) : ShadowG := g + x

def shadowNaturalRegularCopy : Set (ShadowG → ShadowG) :=
  {t | ∃ g : ShadowG, ∀ x : ShadowG,
    t x = shadowNaturalTranslation g x}

def shadowRegularCopy (X : Set (ShadowG → ShadowG)) : Prop :=
  (∀ t : ShadowG → ShadowG, t ∈ X → Function.Bijective t) ∧
    (∀ x y : ShadowG, ∃! t : ShadowG → ShadowG,
      t ∈ X ∧ t x = y)

/-- The quotient-weight shadow counterexample, with the literal section
inequality and the same natural regular translation copy on both sides. -/
def fiveColorShadowDoesNotSupplyActualMap_claim39029 : Prop :=
  ∀ (d₁ d₂ : ShadowD), d₁ ≠ d₂ →
    let S := shadowConnectionSet d₁ d₂
    shadowFiveColorWeightShadow S shadowAlpha ∧
      shadowSection S 1 = ({d₁} : Set ShadowD) ∧
      shadowSection S (-1) = ({d₁} : Set ShadowD) ∧
      shadowSection S 2 = ({d₂} : Set ShadowD) ∧
      shadowSection S (-2) = ({d₂} : Set ShadowD) ∧
      shadowAdditiveAutomorphism shadowAlpha ∧
      (∀ a : ShadowA, shadowWeight S (shadowAlpha a) = shadowWeight S a) ∧
      shadowSection (shadowLiftAlpha '' S) (-2) =
        ({d₁} : Set ShadowD) ∧
      shadowSection (shadowLiftAlpha '' S) (-2) ≠ shadowSection S (-2) ∧
      shadowNaturalRegularCopy = shadowNaturalRegularCopy ∧
      shadowRegularCopy shadowNaturalRegularCopy

end MathlibPlus.Open.ResearchFormalization.R1536
