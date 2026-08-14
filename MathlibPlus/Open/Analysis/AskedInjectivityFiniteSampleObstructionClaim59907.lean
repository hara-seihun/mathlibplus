import Mathlib

namespace MathlibPlus.Open

def askedInjectivityFiniteSampleObstruction_claim59907 : Prop :=
  ∀ (S : Finset ℝ) (a : ℝ),
    let g : ℝ → ℝ := fun _ => 0
    let f : ℝ → ℝ := fun x => (x - a) * Finset.prod S (fun s => (x - s) ^ 2)
    Differentiable ℝ f ∧
      Differentiable ℝ g ∧
      f ≠ g ∧
      f a = g a ∧
      ∀ s ∈ S, deriv f s = deriv g s

end MathlibPlus.Open
