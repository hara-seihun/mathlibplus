import Mathlib

namespace MathlibPlus.Open

noncomputable def rectangleClosed (a b c d : ℝ) : Set ℂ :=
  {z | a ≤ z.re ∧ z.re ≤ b ∧ c ≤ z.im ∧ z.im ≤ d}

def rectangleInterior (a b c d : ℝ) : Set ℂ :=
  {z | a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d}

def rectangleBoundary (a b c d : ℝ) : Set ℂ :=
  rectangleClosed a b c d \ rectangleInterior a b c d

def rectangleCorner (x y : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * Complex.I

def rectangleSegment (p q : ℂ) (s : ℝ) : ℂ :=
  ((1 - s : ℝ) : ℂ) * p + (s : ℂ) * q

noncomputable def rectangleBoundaryPath (a b c d : ℝ) (t : ℝ) : ℂ :=
  if t ≤ (1 / 4 : ℝ) then
    rectangleSegment (rectangleCorner a c) (rectangleCorner b c) (4 * t)
  else if t ≤ (1 / 2 : ℝ) then
    rectangleSegment (rectangleCorner b c) (rectangleCorner b d) (4 * t - 1)
  else if t ≤ (3 / 4 : ℝ) then
    rectangleSegment (rectangleCorner b d) (rectangleCorner a d) (4 * t - 2)
  else
    rectangleSegment (rectangleCorner a d) (rectangleCorner a c) (4 * t - 3)

noncomputable def rectangleRootCount (a b c d : ℝ) (P : Polynomial ℂ) : ℕ := by
  classical
  exact (P.roots.filter (fun z => z ∈ rectangleInterior a b c d)).card

def hasWindingNumber (γ : ℝ → ℂ) (k : ℤ) : Prop :=
  ContinuousOn γ (Set.Icc (0 : ℝ) 1) ∧
    γ 0 = γ 1 ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ≠ 0) ∧
    ∃ θ : ℝ → ℝ,
      ContinuousOn θ (Set.Icc (0 : ℝ) 1) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
          Complex.exp ((θ t : ℂ) * Complex.I) = γ t / (‖γ t‖ : ℂ)) ∧
        θ 1 - θ 0 = 2 * Real.pi * (k : ℝ)

/-- Exact rectangle root count by the winding number of the positively oriented boundary. -/
def exact_rectangle_root_count : Prop :=
  ∀ (a b c d : ℝ) (P : Polynomial ℂ),
    a < b →
    c < d →
    DifferentiableOn ℂ (fun z : ℂ => P.eval z) (rectangleClosed a b c d) →
    (∀ z ∈ rectangleBoundary a b c d, P.eval z ≠ 0) →
    ∀ k : ℤ,
      hasWindingNumber
          (fun t => P.eval (rectangleBoundaryPath a b c d t)) k ↔
        k = (rectangleRootCount a b c d P : ℤ)

end MathlibPlus.Open
