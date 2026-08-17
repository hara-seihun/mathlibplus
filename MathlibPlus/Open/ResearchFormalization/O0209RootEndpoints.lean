import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.O0209RootEndpoints

noncomputable section

/-- The initial cubic in the admitted rational homotopy. -/
def F₀ : ℂ → ℂ := fun x => (x ^ 2 + 1) * (x - 3)

/-- The endpoint cubic in the admitted rational homotopy. -/
def F₁ : ℂ → ℂ := fun x => (x + 2) * (x - 1) * (x - (3 / 2))

/-- The explicitly fixed linear real homotopy, rather than an arbitrary family. -/
def F : ℝ → ℂ → ℂ := fun s x =>
  (1 - (s : ℂ)) * F₀ x + (s : ℂ) * F₁ x

/-- A root is simple when the complex derivative at it is nonzero. -/
def simpleRoot (f : ℂ → ℂ) (z : ℂ) : Prop :=
  f z = 0 ∧ deriv f z ≠ 0

/-- A real root in the open endpoint box `(3/4,7/4)`. -/
def endpointBoxRoot (f : ℂ → ℂ) (z : ℂ) : Prop :=
  f z = 0 ∧
    (3 / 4 : ℝ) < z.re ∧ z.re < (7 / 4 : ℝ) ∧ z.im = 0

/-- Claim 11977: the two endpoint root counts and the endpoint interval
premises for the explicitly admitted cubic homotopy. -/
def claim11977_endpoint_counts : Prop :=
  (∀ z : ℂ, F 0 z = 0 → (0 < z.im ↔ z = Complex.I)) ∧
    simpleRoot (F 0) Complex.I ∧
    (∀ z : ℂ, F 1 z = 0 → z.im = 0) ∧
    (∀ z : ℂ, endpointBoxRoot (F 1) z ↔
      z = (1 : ℂ) ∨ z = (3 / 2 : ℂ)) ∧
    simpleRoot (F 1) (1 : ℂ) ∧
    simpleRoot (F 1) (3 / 2 : ℂ) ∧
    ¬ endpointBoxRoot (F 1) (-2 : ℂ)

end

end MathlibPlus.Open.ResearchFormalization.O0209RootEndpoints
