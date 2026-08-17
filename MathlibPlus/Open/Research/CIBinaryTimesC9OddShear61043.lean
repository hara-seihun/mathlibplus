import Mathlib

namespace MathlibPlus.Open.Research.CIBinaryTimesC9

private def shearMap {V B : Type*} [Add V]
    (φ : B → V) : V × B → V × B :=
  fun p => (p.1 + φ p.2, p.2)

private def shearInverseMap {V B : Type*} [Sub V]
    (φ : B → V) : V × B → V × B :=
  fun p => (p.1 - φ p.2, p.2)

private def relativeDisplacement {V B : Type*} [AddGroup V] [AddGroup B]
    (φ : B → V) (x : V × B) (b : B) : V :=
  φ (b + x.2) - φ x.2 - φ b

private def relativeDerivative {V B : Type*} [AddGroup V] [AddGroup B]
    (φ : B → V) (x : V × B) : Equiv.Perm (V × B) :=
  let d : B → V := relativeDisplacement φ x
  (Equiv.prodComm V B).trans
    ((Equiv.sigmaEquivProd B V).symm.trans
      ((Equiv.sigmaCongrRight
          (fun b : B => Equiv.addRight (d b))).trans
        ((Equiv.sigmaEquivProd B V).trans (Equiv.prodComm B V))))

private def derivativeGroup {V B : Type*} [AddGroup V] [AddGroup B]
    (φ : B → V) : Subgroup (Equiv.Perm (V × B)) :=
  Subgroup.closure (Set.range (relativeDerivative φ))

private def derivativeInvariant {V B : Type*} [AddGroup V] [AddGroup B]
    (φ : B → V) (S : Set (V × B)) : Prop :=
  ∀ p : derivativeGroup φ, p.1 '' S = S

private def shearOrbitContainsImage {V B : Type*} [AddGroup V] [AddGroup B]
    (φ : B → V) (s : V × B) : Prop :=
  ∃ p : derivativeGroup φ, p.1 s = shearMap φ s

private def inverseClosedSet {V B : Type*} [AddGroup V] [AddGroup B]
    (S : Set (V × B)) : Prop :=
  ∀ x, x ∈ S → -x ∈ S

private def oddCoordinateShearRigidityAt
    {V B : Type*} [Fintype V] [AddCommGroup V]
    [Fintype B] [AddCommGroup B] [Module (ZMod 2) V]
    (φ : B → V) : Prop :=
  Function.Bijective (shearMap φ) ∧
    (∀ (x s : V × B),
      relativeDerivative φ x s =
        shearInverseMap φ (shearMap φ (s + x) - shearMap φ x)) ∧
    (∀ s : V × B, shearOrbitContainsImage φ s) ∧
    (∀ S : Set (V × B),
      derivativeInvariant φ S → shearMap φ '' S = S) ∧
    (∀ S : Set (V × B),
      0 ∉ S →
        inverseClosedSet S →
          derivativeInvariant φ S →
            shearMap φ '' S = S)

/-- A shear in an odd additive coordinate moves each point only within its
relative-derivative orbit, so it fixes every invariant connection set. -/
def claim61043_oddCoordinateShearRigidity : Prop :=
  (∀ (V B : Type*) [Fintype V] [AddCommGroup V]
    [Fintype B] [AddCommGroup B] [Module (ZMod 2) V],
    Odd (Fintype.card B) →
      ∀ φ : B → V,
        φ 0 = 0 →
          oddCoordinateShearRigidityAt φ) ∧
  (∀ r : ℕ,
    ∀ φ : (ZMod 9) → (Fin r → ZMod 2),
      φ 0 = 0 →
        oddCoordinateShearRigidityAt φ)

end MathlibPlus.Open.Research.CIBinaryTimesC9
