import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Equality of everywhere-differentiable real functions from equality of their
    derivatives off a countable set and equality at one anchor point. -/
def anchored_derivative_reconstruction_off_countable_set : Prop :=
  ∀ (E : Set ℝ) (f g : ℝ → ℝ),
    E.Countable →
    Differentiable ℝ f →
    Differentiable ℝ g →
    (∀ x : ℝ, x ∉ E → deriv f x = deriv g x) →
    ∀ a : ℝ, f a = g a → f = g

end MathlibPlus.Open.Analysis
