import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The finite Weil functional obtained by summing the Mellin transform over a
finite zero packet. -/
def finiteWeilFunctional {Z V : Type*} [Fintype Z]
    (M : V → Z → ℂ) (h : V) : ℂ :=
  ∑ ρ, M h ρ

/-- The finite Weil form evaluated on a convolution with the sharp reflection. -/
def finiteWeilForm {Z V : Type*} [Fintype Z]
    (convolution : V → V → V)
    (sharp : V → V)
    (M : V → Z → ℂ)
    (f g : V) : ℂ :=
  finiteWeilFunctional M (convolution f (sharp g))

/-- The Mellin reflection form on a finite zero packet. -/
def mellinReflectionForm {Z : Type*} [Fintype Z]
    (τ : Z → Z) (F G : Z → ℂ) : ℂ :=
  ∑ ρ, F ρ * star (G (τ ρ))

/--
The Weil form is the Mellin reflection form in every abstract
Mellin-convolution model.  The model data and its convolution-product,
sharp-reflection, and additive Mellin laws are stated explicitly so that the
finite formula is independent of any analytic realization.
-/
def weilFormEqualsMellinReflectionForm : Prop :=
  ∀ {Z V : Type*} [Fintype Z]
    (convolution : V → V → V)
    (sharp : V → V)
    (M : V → Z → ℂ)
    (τ : Z → Z)
    (add : V → V → V),
    ((∀ (f g : V) (ρ : Z),
        M (convolution f g) ρ = M f ρ * M g ρ) ∧
      (∀ (g : V) (ρ : Z),
        M (sharp g) ρ = star (M g (τ ρ))) ∧
      (∀ (f g : V) (ρ : Z),
        M (add f g) ρ = M f ρ + M g ρ)) →
    ∀ (f g : V),
      finiteWeilForm convolution sharp M f g =
        mellinReflectionForm τ (M f) (M g)

end MathlibPlus.Open.Analysis
