import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.SpecialFunctions

/-- The genus-zero Hadamard product asserted by admitted claim 237 for
`G(z) = K_{iz/2}(β)` at every positive real `β`.

`K` is fixed by its standard positive-real-argument integral.  "Entire of order
one" is stated by the usual two-sided epsilon growth characterization: growth is
at most `exp (|z|^(1+ε))` for every positive `ε`, and is not at most any positive
multiple of `exp (|z|^(1-ε))`.  The sequence `τ` enumerates the positive zeros,
including repetitions if multiplicities require them. -/
def besselKGenusZeroHadamardProduct : Prop :=
  let besselK : ℂ → ℝ → ℂ := fun ν β =>
    ∫ t in Set.Ioi (0 : ℝ),
      Complex.exp (-((β : ℂ) * Complex.cosh (t : ℂ))) *
        Complex.cosh (ν * (t : ℂ))
  ∀ β : ℝ, 0 < β →
    let G : ℂ → ℂ := fun z => besselK (Complex.I * z / 2) β
    Function.Even G ∧
      (∀ x : ℝ, (G (x : ℂ)).im = 0) ∧
      Differentiable ℂ G ∧
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
        ∀ z : ℂ, ‖G z‖ ≤ C * Real.exp (Real.rpow ‖z‖ (1 + ε))) ∧
      (∀ ε : ℝ, 0 < ε → ∀ C : ℝ, 0 < C →
        ∃ z : ℂ, C * Real.exp (Real.rpow ‖z‖ (1 - ε)) < ‖G z‖) ∧
      ∃ τ : ℕ → ℝ,
        (∀ j, 0 < τ j) ∧
        (∀ z : ℂ, G z = 0 ↔
          ∃ j, z = (τ j : ℂ) ∨ z = -(τ j : ℂ)) ∧
        Summable (fun j => ((τ j) ^ 2)⁻¹) ∧
        (∀ z : ℂ, G z = G 0 *
          ∏' j : ℕ, (1 - z ^ 2 / ((τ j : ℂ) ^ 2))) ∧
        G 0 = besselK 0 β ∧
        0 < (besselK 0 β).re

end MathlibPlus.Open.Analysis.SpecialFunctions
