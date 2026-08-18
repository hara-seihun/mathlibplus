import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim61229

abbrev Base (p : ℕ) := ZMod p × ZMod p

/-- The vertical displacement subspace attached to a base increment. -/
def displacementSpan {p : ℕ} {Z : Type*} [AddCommGroup Z]
    [Module (ZMod p) Z] (F : Base p → Z) (b : Base p) :
    Submodule (ZMod p) Z :=
  Submodule.span (ZMod p)
    (Set.range (fun a : Base p => F b + F a - F (a + b)))

/-- The normalized vertical shear over the two-dimensional base. -/
def verticalShear {p : ℕ} {Z : Type*} [AddCommGroup Z]
    [Module (ZMod p) Z] (F : Base p → Z) :
    (Base p × Z) → (Base p × Z) :=
  fun x => (x.1, x.2 + F x.1)

/-- The linear shadow shear attached to a linear correction. -/
def linearShadowShear {p : ℕ} {Z : Type*} [AddCommGroup Z]
    [Module (ZMod p) Z] (ell : Base p →ₗ[ZMod p] Z) :
    (Base p × Z) → (Base p × Z) :=
  fun x => (x.1, x.2 + ell x.1)

/-- A pointed directed additive Cayley-relation isomorphism. -/
def pointedCayleyRelationIso {G : Type*} [AddGroup G]
    (q : G → G) (S T : Set G) : Prop :=
  q 0 = 0 ∧
    Function.Bijective q ∧
      ∀ x y, y - x ∈ S ↔ q y - q x ∈ T

/-- Identity-freeness and inverse closure for ordinary additive connection sets. -/
def identityFree {G : Type*} [AddZeroClass G] (S : Set G) : Prop :=
  0 ∉ S

def inverseClosed {G : Type*} [AddGroup G] (S : Set G) : Prop :=
  ∀ x, x ∈ S ↔ -x ∈ S

/-- The displayed linear shadow is literally an additive group automorphism. -/
def realizesLinearShadow {p : ℕ} {Z : Type*} [AddCommGroup Z]
    [Module (ZMod p) Z] (ell : Base p →ₗ[ZMod p] Z) : Prop :=
  ∃ L : (Base p × Z) ≃+ (Base p × Z),
    ∀ x, L x = linearShadowShear ell x

/-- Claim 61229: every normalized shear over `F_p^2` has one linear
connection-set shadow, with no restriction on the finite-dimensional fibre. -/
def claim61229 : Prop :=
  ∀ (p : ℕ), (hp : p.Prime) →
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    ∀ (Z : Type*) [AddCommGroup Z] [Module (ZMod p) Z]
      [FiniteDimensional (ZMod p) Z],
      ∀ F : Base p → Z, F 0 = 0 →
        ∃ ell : Base p →ₗ[ZMod p] Z,
          (∀ b : Base p, F b - ell b ∈ displacementSpan F b) ∧
          realizesLinearShadow ell ∧
          ∀ S T : Set (Base p × Z),
            pointedCayleyRelationIso (verticalShear F) S T →
              Set.image (linearShadowShear ell) S = T ∧
                ((identityFree S ∧ inverseClosed S) ↔
                  (identityFree T ∧ inverseClosed T))

end MathlibPlus.Open.ResearchFormalization.Claim61229
