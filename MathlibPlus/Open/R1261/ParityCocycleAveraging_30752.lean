import Mathlib

namespace MathlibPlus.Open.R1261

open scoped BigOperators

private def supportStabilizer (D : Type*) [Group D] [Fintype D] : Prop :=
  Nonempty (D ≃* Multiplicative (ZMod 1)) ∨
    Nonempty (D ≃* Multiplicative (ZMod 4)) ∨
      Nonempty (D ≃* QuaternionGroup 3)

private def paritySign {D : Type*} [Group D]
    (χ : D →* Multiplicative (ZMod 2)) (d : D) (m : ℕ) : ZMod m :=
  if Multiplicative.toAdd (χ d) = 0 then 1 else -1

private def twistedCocycle {D : Type*} [Group D]
    (χ : D →* Multiplicative (ZMod 2)) (m : ℕ)
    (τ : D → ZMod m) : Prop :=
  ∀ d e : D,
    τ (d * e) = τ d + paritySign χ d m * τ e

private def averagedCocycleFormula {D : Type*} [Group D] [Fintype D]
    (χ : D →* Multiplicative (ZMod 2)) (m : ℕ)
    (τ : D → ZMod m) : Prop :=
  let c : ZMod m :=
    (Fintype.card D : ZMod m)⁻¹ * ∑ e : D, τ e
  (∀ d : D, τ d = c * (1 - paritySign χ d m)) ∧
    (∀ (d : D) (z : ZMod m),
      paritySign χ d m * (z + c) + τ d - c =
        paritySign χ d m * z)

/-- Claim 30752: in each of the three exact support-stabilizer cases, a
coprime parity-twisted cyclic cocycle is the displayed averaged coboundary;
the second conjunct is the corresponding global torus correction. -/
def claim30752 : Prop :=
  ∀ (D : Type*) [Group D] [Fintype D]
    (χ : D →* Multiplicative (ZMod 2)),
    supportStabilizer D →
    ∀ m : ℕ, 1 < m → Nat.Coprime m (Fintype.card D) →
      ∀ τ : D → ZMod m,
        twistedCocycle χ m τ →
        averagedCocycleFormula χ m τ

end MathlibPlus.Open.R1261
