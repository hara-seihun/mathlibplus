import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- Positive real numbers, the carrier used for multiplicative test functions. -/
abbrev PositiveReal := {x : ℝ // 0 < x}

/-- Extend a function on the positive reals by zero to the real line. -/
def positiveExtension (f : PositiveReal → ℂ) : ℝ → ℂ :=
  fun x => if hx : 0 < x then f ⟨x, hx⟩ else 0

/-- The compactly supported smooth positive-real test-function carrier. -/
def TestFunction (f : PositiveReal → ℂ) : Prop :=
  ContDiff ℝ ⊤ (positiveExtension f) ∧ HasCompactSupport (positiveExtension f)

/-- Mellin transform with the convention `∫ f(x) x^s dx/x`. -/
def mellinTransform (f : PositiveReal → ℂ) (s : ℂ) : ℂ :=
  ∫ x in Set.Ioi (0 : ℝ),
    positiveExtension f x * Complex.cpow (x : ℂ) s / (x : ℂ)

/-- The sharp operation on positive-real functions. -/
def sharp (f : PositiveReal → ℂ) (x : PositiveReal) : ℂ :=
  ((x : ℝ)⁻¹ : ℂ) * star (f ⟨(x : ℝ)⁻¹, inv_pos.mpr x.property⟩)

/-- Mellin transform of sharp, with `τ(s) = 1 - conj(s)`. -/
def mellinTransformSharp : Prop :=
  ∀ (f : PositiveReal → ℂ), TestFunction f → ∀ s : ℂ,
    let F : ℂ → ℂ := mellinTransform f
    let τ : ℂ → ℂ := fun z => 1 - star z
    mellinTransform (sharp f) s = star (mellinTransform f (1 - star s)) ∧
      star (mellinTransform f (1 - star s)) = star (F (τ s))

end

end MathlibPlus.Open.Analysis
