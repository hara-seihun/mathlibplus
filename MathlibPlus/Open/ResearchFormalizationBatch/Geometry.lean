import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch.Geometry

open scoped RealInnerProductSpace

noncomputable section

abbrev Vec2 := EuclideanSpace ℝ (Fin 2)

def det2 (u v : Vec2) : ℝ :=
  u 0 * v 1 - u 1 * v 0

def inner2 (u v : Vec2) : ℝ :=
  @inner ℝ Vec2 (inferInstance : Inner ℝ Vec2) u v

def unitSeparated (X : Set Vec2) : Prop :=
  ∀ ⦃x y : Vec2⦄, x ∈ X → y ∈ X → x ≠ y → 1 ≤ ‖x - y‖

def noUnitEquilateral (X : Set Vec2) : Prop :=
  ¬ ∃ x y z : Vec2,
    x ∈ X ∧ y ∈ X ∧ z ∈ X ∧ x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      ‖x - y‖ = 1 ∧ ‖y - z‖ = 1 ∧ ‖z - x‖ = 1

def previousIndex {p : ℕ} (i : Fin p) : Fin (p + 1) :=
  ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩

def nextIndex {p : ℕ} (i : Fin p) : Fin (p + 1) :=
  ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

/-- A complete Cartesian product of unit rhombus tracks with variable
    directions. -/
def completeVariableDirectionUnitRhombusChart
    (X : Set Vec2) (p q : ℕ) (x00 : Vec2)
    (U : Fin (p + 1) → Vec2) (V : Fin (q + 1) → Vec2)
    (u : Fin p → Vec2) (v : Fin q → Vec2) : Prop :=
  1 ≤ p ∧ 1 ≤ q ∧
  unitSeparated X ∧ noUnitEquilateral X ∧
  U 0 = 0 ∧ V 0 = 0 ∧
  (∀ i : Fin p, ‖u i‖ = 1 ∧ U (nextIndex i) - U (previousIndex i) = u i) ∧
  (∀ j : Fin q, ‖v j‖ = 1 ∧ V (nextIndex j) - V (previousIndex j) = v j) ∧
  (Function.Injective
    (fun ij : Fin (p + 1) × Fin (q + 1) => x00 + U ij.1 + V ij.2)) ∧
  (∀ i : Fin (p + 1), ∀ j : Fin (q + 1),
    x00 + U i + V j ∈ X) ∧
  ((∀ i : Fin p, ∀ j : Fin q, 0 < det2 (u i) (v j)) ∨
    (∀ i : Fin p, ∀ j : Fin q, det2 (u i) (v j) < 0))

/-- Reversing one of the two track orientations makes all crossings positive,
    and the forbidden unit equilateral triangle gives the strict angle bounds. -/
def strictCrossingAngleLemma : Prop :=
  ∀ (X : Set Vec2) (p q : ℕ) (x00 : Vec2)
    (U : Fin (p + 1) → Vec2) (V : Fin (q + 1) → Vec2)
    (u : Fin p → Vec2) (v : Fin q → Vec2),
    completeVariableDirectionUnitRhombusChart X p q x00 U V u v →
    (((∀ i : Fin p, ∀ j : Fin q, 0 < det2 (u i) (v j)) ∨
      (∀ i : Fin p, ∀ j : Fin q, 0 < det2 (-u i) (v j))) ∧
    (∀ i : Fin p, ∀ j : Fin q,
      -(1 / 2 : ℝ) < inner2 (u i) (v j) ∧
      inner2 (u i) (v j) < 1 / 2 ∧
      Real.pi / 3 < Real.arccos (inner2 (u i) (v j)) ∧
      Real.arccos (inner2 (u i) (v j)) < 2 * Real.pi / 3))

end
end MathlibPlus.Open.ResearchFormalizationBatch.Geometry
