import Mathlib

namespace MathlibPlus.Open.Research.R1184BasePlaneShear

noncomputable section

abbrev B := Fin 2 → ZMod 3
abbrev RankShearCarrier (r : ℕ) := B × (Fin (r - 2) → ZMod 3)

def displacementSpan {Z : Type*} [AddCommGroup Z] [Module (ZMod 3) Z]
    (F : B → Z) (b : B) : Submodule (ZMod 3) Z :=
  Submodule.span (ZMod 3)
    {z | ∃ a : B, z = F b + F a - F (a + b)}

def qShear {Z : Type*} [AddCommGroup Z] [Module (ZMod 3) Z]
    (F : B → Z) : B × Z → B × Z :=
  fun x => (x.1, x.2 + F x.1)

def linearShear {Z : Type*} [AddCommGroup Z] [Module (ZMod 3) Z]
    (ell : B →ₗ[ZMod 3] Z) : B × Z → B × Z :=
  fun x => (x.1, x.2 + ell x.1)

def realizesLinearShearEquiv {Z : Type*}
    [AddCommGroup Z] [Module (ZMod 3) Z]
    (ell : B →ₗ[ZMod 3] Z) : Prop :=
  ∃ L : (B × Z) ≃ₗ[ZMod 3] (B × Z),
    ∀ x, L x = linearShear ell x

def additiveIdentityFree {G : Type*} [AddZeroClass G]
    (S : Set G) : Prop :=
  0 ∉ S

def additiveInverseClosed {G : Type*} [AddGroup G]
    (S : Set G) : Prop :=
  ∀ x, x ∈ S → -x ∈ S

def pointedCayleyRelationIso {G : Type*} [AddGroup G]
    (q : G → G) (S T : Set G) : Prop :=
  q 0 = 0 ∧
    Function.Bijective q ∧
    ∀ x y, y - x ∈ S ↔ q y - q x ∈ T

def ternaryBasePlaneShearShadow {Z : Type*}
    [AddCommGroup Z] [Module (ZMod 3) Z] [FiniteDimensional (ZMod 3) Z] : Prop :=
  ∀ F : B → Z, F 0 = 0 →
    ∃ ell : B →ₗ[ZMod 3] Z,
      ∀ b : B, F b - ell b ∈ displacementSpan F b

def ternaryBasePlaneConnectionShadow {Z : Type*}
    [AddCommGroup Z] [Module (ZMod 3) Z] [FiniteDimensional (ZMod 3) Z] : Prop :=
  ∀ F : B → Z, F 0 = 0 →
    ∀ S T : Set (B × Z),
      pointedCayleyRelationIso (qShear F) S T →
      ∃ ell : B →ₗ[ZMod 3] Z,
        (∀ b : B, F b - ell b ∈ displacementSpan F b) ∧
        realizesLinearShearEquiv ell ∧
        Set.image (linearShear ell) S = T

def rankShearIdentityFreeInverseClosedShadow : Prop :=
  ∀ r : ℕ, (r = 6 ∨ r = 7) →
    ∀ F : B → (Fin (r - 2) → ZMod 3), F 0 = 0 →
      ∀ S T : Set (RankShearCarrier r),
        additiveIdentityFree S →
        additiveIdentityFree T →
        additiveInverseClosed S →
        additiveInverseClosed T →
        pointedCayleyRelationIso (qShear F) S T →
        ∃ ell : B →ₗ[ZMod 3] (Fin (r - 2) → ZMod 3),
          realizesLinearShearEquiv ell ∧
          Set.image (linearShear ell) S = T

/-- Claim 61028. -/
def claim61028 : Prop :=
  (∀ (Z : Type*) [AddCommGroup Z] [Module (ZMod 3) Z]
      [FiniteDimensional (ZMod 3) Z],
    ternaryBasePlaneShearShadow (Z := Z)) ∧
  (∀ (Z : Type*) [AddCommGroup Z] [Module (ZMod 3) Z]
      [FiniteDimensional (ZMod 3) Z],
    ternaryBasePlaneConnectionShadow (Z := Z)) ∧
  rankShearIdentityFreeInverseClosedShadow

end

end MathlibPlus.Open.Research.R1184BasePlaneShear
