import Mathlib

namespace MathlibPlus.Open.Analysis.Claim48431

open Polynomial

/-- The source physical exact-delay factorization carrier. -/
def physicalExactDelayCarrier {R : Type*} [CommRing R]
    (ρ : R) (S : Polynomial R) : Prop :=
  ∃ (k : ℕ) (g d : Polynomial R),
    0 < k ∧ d.eval ρ = 0 ∧ S = Polynomial.X ^ k * g * d

/-- Componentwise scaling of a ternary family of physical carriers. -/
def scaledTernaryExactDelayCarrier {R : Type*} [CommRing R]
    (ρ : R) (S : Fin 3 → Polynomial R) : Prop :=
  ∀ i : Fin 3, physicalExactDelayCarrier ρ (S i)

/-- Claim 48431: physical exact-delay carrier normals vanish at both universal
points, and the same endpoint vanishing holds componentwise after scaling. -/
def claim48431_exactDelayCarrierNormals : Prop :=
  ∀ {R : Type*} [CommRing R] (ρ : R),
    (∀ S : Polynomial R,
      physicalExactDelayCarrier ρ S →
        S.eval 0 = 0 ∧ S.eval ρ = 0 ∧
          ∀ weight : R, (weight • S).eval 0 = 0 ∧ (weight • S).eval ρ = 0) ∧
    (∀ (A : Fin 3 → Polynomial R) (weights : Fin 3 → R),
      scaledTernaryExactDelayCarrier ρ A →
        ∀ i : Fin 3,
          (weights i • A i).eval 0 = 0 ∧ (weights i • A i).eval ρ = 0)

end MathlibPlus.Open.Analysis.Claim48431
