import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- The value of the normalized derivative in Claim 27024. -/
def normalizedDerivativeValue
    {G : Type*} [Group G] (f : G ≃ G) (g c : G) : G :=
  f (c * g) * (f g)⁻¹

/-- Claim 27024: normalized derivatives and their relative derivative group. -/
def normalizedDerivativeAndRelativeDerivativeGroup
    {G : Type*} [Group G] [Fintype G]
    (f : G ≃ G) (d : G → Equiv.Perm G)
    (Δ : Subgroup (Equiv.Perm G)) : Prop :=
  f 1 = 1 ∧
    (∀ g c, d g c = normalizedDerivativeValue f g c) ∧
      Δ =
        Subgroup.closure
          {p : Equiv.Perm G |
            ∃ g : G, p = (d g).trans f.symm} ∧
        (∀ p, p ∈ Δ → p 1 = 1)

/-- The factor subgroup carrier inside a direct product. -/
def vFactorCarrier
    {V H : Type*} [Group V] [Group H] (x : V × H) : Prop :=
  x.2 = 1

/-- Characteristicity of the V factor in the direct product. -/
def vFactorCharacteristic
    {V H : Type*} [Group V] [Group H] : Prop :=
  ∀ e : (V × H) ≃* (V × H),
    ∀ x : V × H, vFactorCarrier x ↔ vFactorCarrier (e x)

/-- Preservation of the cosets of the V factor. -/
def preservesVFactorCosets
    {V H : Type*} [Group V] [Group H]
    (f : (V × H) ≃ (V × H)) : Prop :=
  ∀ h : H, ∃ h' : H,
    (∀ v : V, (f (v, h)).2 = h') ∧
      (∀ x : V × H, x.2 = h' → ∃ v : V, f (v, h) = x)

/-- Claim 27676: fiber-preserving normalized bijections have the stated form. -/
def fiberPreservingNormalizedMapForm
    {V H : Type*} [Group V] [Group H] : Prop :=
  vFactorCharacteristic (V := V) (H := H) →
    ∀ f : (V × H) ≃ (V × H),
      f (1, 1) = (1, 1) →
        preservesVFactorCosets f →
          ∃ (φ : H → V → V) (σ : H → H),
            Function.Bijective σ ∧
              σ 1 = 1 ∧
                ∀ v h, f (v, h) = (φ h v, σ h)

end MathlibPlus.Open.ResearchFormalization
