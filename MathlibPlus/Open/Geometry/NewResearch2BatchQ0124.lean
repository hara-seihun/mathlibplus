import Mathlib

namespace MathlibPlus.Open.Geometry

/-- Claim 16687: the exact minimum-distance diameter-minimizer property for a
finite planar configuration of fixed cardinality. -/
def newResearch2Claim16687
    (n : ℕ) (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  A.card = n ∧
    (∀ x ∈ A, ∀ y ∈ A, x ≠ y → 1 ≤ dist x y) ∧
    (∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ dist x y = 1) ∧
    (∀ B : Finset (EuclideanSpace ℝ (Fin 2)),
      (B.card = n ∧
        (∀ x ∈ B, ∀ y ∈ B, x ≠ y → 1 ≤ dist x y) ∧
        (∃ x ∈ B, ∃ y ∈ B, x ≠ y ∧ dist x y = 1)) →
      Metric.diam (A : Set (EuclideanSpace ℝ (Fin 2))) ≤
        Metric.diam (B : Set (EuclideanSpace ℝ (Fin 2))))

/-- Claim 16689: the four vertices of a unit square satisfy the minimizer
property while containing no unit equilateral triangle. -/
def newResearch2Claim16689 : Prop :=
  let p₀₀ : EuclideanSpace ℝ (Fin 2) :=
    (EuclideanSpace.equiv (Fin 2) ℝ).symm ![(0 : ℝ), (0 : ℝ)]
  let p₁₀ : EuclideanSpace ℝ (Fin 2) :=
    (EuclideanSpace.equiv (Fin 2) ℝ).symm ![(1 : ℝ), (0 : ℝ)]
  let p₀₁ : EuclideanSpace ℝ (Fin 2) :=
    (EuclideanSpace.equiv (Fin 2) ℝ).symm ![(0 : ℝ), (1 : ℝ)]
  let p₁₁ : EuclideanSpace ℝ (Fin 2) :=
    (EuclideanSpace.equiv (Fin 2) ℝ).symm ![(1 : ℝ), (1 : ℝ)]
  let A : Finset (EuclideanSpace ℝ (Fin 2)) := {p₀₀, p₁₀, p₀₁, p₁₁}
  newResearch2Claim16687 4 A ∧
    ¬ ∃ x y z : EuclideanSpace ℝ (Fin 2),
      x ∈ A ∧ y ∈ A ∧ z ∈ A ∧
      x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      dist x y = 1 ∧ dist x z = 1 ∧ dist y z = 1

end MathlibPlus.Open.Geometry
