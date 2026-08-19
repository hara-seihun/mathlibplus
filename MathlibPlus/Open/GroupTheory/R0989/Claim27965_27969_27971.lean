import Mathlib

namespace MathlibPlus.Open.GroupTheory.R0989

noncomputable section

/-- Claim 27965: normalized relative derivatives give the exact image
criterion for a Cayley neighborhood, without an inverse-closure assumption. -/
def groupUniversalNormalizedDerivativeCriterion_claim27965 : Prop :=
  ∀ (G : Type*) [Group G] [Finite G]
    (f : Equiv.Perm G) (S : Set G),
    f 1 = 1 →
      (∀ g : G,
        ((fun c : G => f.symm (f (c * g) * (f g)⁻¹)) '' S = S ↔
          (fun c : G => f (c * g) * (f g)⁻¹) '' S = f '' S)) ∧
      ((∀ g : G, (fun c : G => f (c * g) * (f g)⁻¹) '' S = f '' S) ↔
        ∀ g : G,
          (fun c : G => f.symm (f (c * g) * (f g)⁻¹)) '' S = S)

abbrev C2Cube := Fin 3 → ZMod 2

noncomputable def cubeDerivative
    (σ : Equiv.Perm C2Cube) (u : C2Cube) : Equiv.Perm C2Cube :=
  ((Equiv.addRight u).trans σ).trans
    ((Equiv.addRight (σ u)).trans σ.symm)

noncomputable def cubeDerivativeGroup
    (σ : Equiv.Perm C2Cube) : Subgroup (Equiv.Perm C2Cube) :=
  Subgroup.closure (Set.range (cubeDerivative σ))

/-- Claim 27969: one global `GL(3,2)` shadow transports every derivative
orbit and every union of derivative orbits. -/
def globalLinearDerivativeShadow_claim27969 : Prop :=
  ∀ σ : Equiv.Perm C2Cube, σ 0 = 0 →
    ∃ L : C2Cube ≃+ C2Cube,
      (∀ O : Set C2Cube,
        (∃ x : C2Cube,
          O = {y : C2Cube | ∃ p : cubeDerivativeGroup σ, p.1 x = y}) →
          L '' O = σ '' O) ∧
      (∀ S : Set C2Cube,
        (∀ x : C2Cube, ∀ p : cubeDerivativeGroup σ,
          x ∈ S ↔ p.1 x ∈ S) →
          L '' S = σ '' S)

/-- Claim 27971: the pure base map on `C₂³ × B` is harmless over every finite
direct factor; derivative invariance yields one common additive linear shadow. -/
def pureBaseMapsAreHarmless_claim27971 : Prop :=
  ∀ (B : Type*) [Group B] [Finite B]
    (σ : Equiv.Perm C2Cube),
    σ 0 = 0 →
    ∀ S : Set (C2Cube × B),
      (∀ (u : C2Cube) (t : B) (x : C2Cube) (b : B),
        ((x, b) ∈ S ↔
          (σ.symm (σ (x + u) + σ u), (b * t) * t⁻¹) ∈ S)) →
      ∃ L : C2Cube ≃+ C2Cube,
        (fun z : C2Cube × B => (σ z.1, z.2)) '' S =
          (fun z : C2Cube × B => (L z.1, z.2)) '' S

end

end MathlibPlus.Open.GroupTheory.R0989
