import Mathlib

open scoped BigOperators
open scoped Topology
open MeasureTheory
open Set
open Filter

namespace MathlibPlus.Open.ResearchFormalizationLargeBatch
def claim6775_augmentationCoupledPlaneModule : Prop := by
  classical
  exact ∀ (X : Type*) [AddCommGroup X] [Fintype X]
    [Module (ZMod 3) X] [FiniteDimensional (ZMod 3) X]
    (u : X) (U : Submodule (ZMod 3) X),
    u ≠ 0 → U = Submodule.span (ZMod 3) ({u} : Set X) →
    ∀ (h : X), h ∈ U → h ≠ 0 →
      let R := ZMod 3
      let D := R × R
      let a : D := (1, 0)
      let b : D := (0, 1)
      let W_U : Set (X → R) :=
        {w | ∀ x : X,
          ∑ z ∈ Finset.univ.filter (fun z : X => z - x ∈ U), w z = 0}
      let k_w : (X → R) → (X → D) := fun w x =>
        w x • a + w (x - h) • b
      let M_h : Set (X → D) :=
        {k | ∃ w, w ∈ W_U ∧ k = k_w w}
      (∀ k, k ∈ M_h ↔ ∃ w, w ∈ W_U ∧ k = k_w w) ∧
        0 ∈ M_h ∧
        (∀ (r : R) k, k ∈ M_h → r • k ∈ M_h) ∧
        (∀ k l, k ∈ M_h → l ∈ M_h → k + l ∈ M_h)

def claim6776_offLineDifferenceImageIsFullPlane : Prop := by
  classical
  exact ∀ (X : Type*) [AddCommGroup X] [Fintype X]
    [Module (ZMod 3) X] [FiniteDimensional (ZMod 3) X]
    (u : X) (U : Submodule (ZMod 3) X),
    u ≠ 0 → U = Submodule.span (ZMod 3) ({u} : Set X) →
    ∀ (h : X), h ∈ U → h ≠ 0 →
      let R := ZMod 3
      let D := R × R
      let a : D := (1, 0)
      let b : D := (0, 1)
      let W_U : Set (X → R) :=
        {w | ∀ z : X,
          ∑ y ∈ Finset.univ.filter (fun y : X => y - z ∈ U), w y = 0}
      let k_w : (X → R) → (X → D) := fun w z =>
        w z • a + w (z - h) • b
      let M_h : Set (X → D) :=
        {k | ∃ w, w ∈ W_U ∧ k = k_w w}
      ∀ x y, y - x ∉ U →
        {d : D | ∃ k, k ∈ M_h ∧ d = k y - k x} = Set.univ

def claim6777_onLineDifferenceImageIsDiagonalLine : Prop := by
  classical
  exact ∀ (X : Type*) [AddCommGroup X] [Fintype X]
    [Module (ZMod 3) X] [FiniteDimensional (ZMod 3) X]
    (u : X) (U : Submodule (ZMod 3) X),
    u ≠ 0 → U = Submodule.span (ZMod 3) ({u} : Set X) →
    ∀ (h : X), h ∈ U → h ≠ 0 →
      let R := ZMod 3
      let D := R × R
      let a : D := (1, 0)
      let b : D := (0, 1)
      let W_U : Set (X → R) :=
        {w | ∀ z : X,
          ∑ y ∈ Finset.univ.filter (fun y : X => y - z ∈ U), w y = 0}
      let k_w : (X → R) → (X → D) := fun w z =>
        w z • a + w (z - h) • b
      let M_h : Set (X → D) :=
        {k | ∃ w, w ∈ W_U ∧ k = k_w w}
      ∀ x y, y - x ∈ U → y - x ≠ 0 →
        {d : D | ∃ k, k ∈ M_h ∧ d = k y - k x} =
          (Submodule.span R ({a + b} : Set D) : Set D)

end MathlibPlus.Open.ResearchFormalizationLargeBatch
