import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1395Claim38581

open Set

private def rho0 : Equiv.Perm (Fin 8) :=
  Equiv.swap 6 7

private def baseOrbitFamily : Set (Set (Fin 8)) :=
  {O |
    O = ({0} : Set (Fin 8)) ∨
      O = ({1} : Set (Fin 8)) ∨
      O = ({2, 3} : Set (Fin 8)) ∨
      O = ({4, 5} : Set (Fin 8)) ∨
      O = ({6, 7} : Set (Fin 8))}

private def fullCylinder {B : Type*} (O : Set (Fin 8)) : Set (Fin 8 × B) :=
  O ×ˢ (Set.univ : Set B)

private def record8OrbitFamily {B : Type*} : Set (Set (Fin 8 × B)) :=
  {S |
    (∃ O : Set (Fin 8),
      baseOrbitFamily O ∧ O ≠ ({0} : Set (Fin 8)) ∧
        S = fullCylinder O) ∨
    (∃ b : B, S = ({(0, b)} : Set (Fin 8 × B)))}

private def isNormalizedOrbitUnion {B : Type*} (S : Set (Fin 8 × B)) : Prop :=
  ∀ O : Set (Fin 8 × B), record8OrbitFamily O →
    (O ⊆ S ∨ Disjoint O S)

private def support {B : Type*} (q : Fin 8 → B → B) : Set (Fin 8) :=
  {a | q a ≠ (fun b => b)}

private def nonidentityTranslation {B : Type*} [AddCommGroup B]
    (q : B → B) : Prop :=
  (∃ t : B, (∀ b : B, q b = b + t) ∧ q ≠ (fun b => b))

private def displacementSubgroup {B : Type*} [AddCommGroup B]
    (q : B → B) : AddSubgroup B :=
  AddSubgroup.closure (Set.range (fun t : B => t - q t + q 0))

private def fiberMap {B : Type*} (q : Fin 8 → B → B) :
    Fin 8 × B → Fin 8 × B :=
  fun p => (rho0 p.1, q p.1 p.2)

/-- Claim 38581: the displayed support-four fibre map fixes every full
nonzero cylinder (and every point of the zero fibre), so the same orbit
preservation is available in both directed and ordinary-undirected scopes. -/
def cylinderPreservationSimultaneousCIDCI_claim38581 : Prop :=
  ∀ (B : Type*) [Fintype B] [AddCommGroup B],
    Odd (Fintype.card B) →
    ∀ (q : Fin 8 → B → B),
      (∀ a : Fin 8, Function.Bijective (q a)) →
      support q = ({1, 2, 3, 4} : Set (Fin 8)) →
      nonidentityTranslation (q 1) ∧
        nonidentityTranslation (q 2) ∧
        nonidentityTranslation (q 3) →
      displacementSubgroup (q 4) = ⊤ →
      (∀ O : Set (Fin 8), baseOrbitFamily O → Set.image rho0 O = O) ∧
        (∀ b : B, fiberMap q (0, b) = (0, b)) ∧
        (∀ O : Set (Fin 8),
          baseOrbitFamily O → O ≠ ({0} : Set (Fin 8)) →
            Set.image (fiberMap q) (fullCylinder O) = fullCylinder O) ∧
        (∀ O : Set (Fin 8 × B), record8OrbitFamily O →
          Set.image (fiberMap q) O = O) ∧
        (∀ S : Set (Fin 8 × B), isNormalizedOrbitUnion S →
          Set.image (fiberMap q) S = S) ∧
        (∀ S : Set (Fin 8 × B), isNormalizedOrbitUnion S →
          Set.image (fiberMap q) S = S)

end MathlibPlus.Open.ResearchFormalization.R1395Claim38581
