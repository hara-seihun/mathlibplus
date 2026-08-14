import Mathlib

namespace MathlibPlus.Open.Research.FiberSupport

noncomputable section

/-- `C₂³`, written as the additive group of functions from three coordinates. -/
abbrev A8 := Fin 3 → ZMod 2

def fiberMap {B : Type*} [Zero B] (σ : Equiv.Perm A8) (q : A8 → Equiv.Perm B) :
    A8 × B → A8 × B :=
  fun p => (σ p.1, q p.1 p.2)

def normalizedFiberMap {B : Type*} [Zero B] (σ : Equiv.Perm A8)
    (q : A8 → Equiv.Perm B) : Prop :=
  fiberMap σ q (0, 0) = (0, 0)

def activeSupport {B : Type*} (q : A8 → Equiv.Perm B) : Set A8 :=
  {a | a ≠ 0 ∧ q a ≠ 1}

def displacementSubgroup {B : Type*} [AddCommGroup B]
    (q : Equiv.Perm B) : AddSubgroup B :=
  AddSubgroup.closure (Set.range (fun b : B => q b - b))

def fullDisplacement {B : Type*} [AddCommGroup B]
    (q : A8 → Equiv.Perm B) : Prop :=
  ∀ c : A8, c ∈ activeSupport q → displacementSubgroup (q c) = ⊤

/-- The active-support and full-displacement hypotheses for a normalized
fiber map over a finite odd-order abelian group. -/
def claim28544 {B : Type*} [AddCommGroup B] [Fintype B]
    (_hOdd : Odd (Fintype.card B)) (σ : Equiv.Perm A8)
    (q : A8 → Equiv.Perm B) : Prop :=
  Odd (Fintype.card B) ∧ normalizedFiberMap σ q ∧
    (∀ a : A8, a ∈ activeSupport q ↔ a ≠ 0 ∧ q a ≠ 1) ∧
    fullDisplacement q

end
end MathlibPlus.Open.Research.FiberSupport
