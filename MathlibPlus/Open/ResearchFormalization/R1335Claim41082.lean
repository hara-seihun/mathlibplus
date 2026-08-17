import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1335

namespace Claim41082

noncomputable section

abbrev F5 := ZMod 5

/-- The translation by an exponent in the fixed `C₅` action. -/
def rotationBy {X : Type*} (a : F5) : Equiv.Perm (F5 × X) :=
  Equiv.prodCongr (Equiv.addRight a) (Equiv.refl X)

abbrev rotation {X : Type*} : Equiv.Perm (F5 × X) :=
  rotationBy 1

/-- Conjugation of the fixed global rotation by a coordinate permutation. -/
def conjugatesRotation {X : Type*}
    (f : Equiv.Perm (F5 × X)) (lam : F5) : Prop :=
  f * rotation * f.symm = rotationBy lam

/-- A normalizer coordinate expression with a prescribed multiplier. -/
def affineCoordinate {X : Type*}
    (f : Equiv.Perm (F5 × X)) (lam : F5)
    (τ : X → F5) (σ : Equiv.Perm X) : Prop :=
  ∀ z : F5, ∀ x : X,
    f (z, x) = (lam * z + τ x, σ x)

/-- Claim 41082: the exponent in `f ρ f⁻¹ = ρ^λ` is the same slope on
all `P`-orbits, rather than an independently chosen slope on each block. -/
def globalSlopeNormalizer_claim41082 : Prop :=
  ∀ {X : Type*} [Fintype X] (hX : Nonempty X)
    (f : Equiv.Perm (F5 × X)) (lam : F5),
    lam ≠ 0 →
      conjugatesRotation f lam →
        ∃! q : (X → F5) × Equiv.Perm X,
          affineCoordinate f lam q.1 q.2

end

end Claim41082

end MathlibPlus.Open.ResearchFormalization.R1335
