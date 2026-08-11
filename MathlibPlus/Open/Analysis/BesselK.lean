import Mathlib

/-!
# Zeros of the imaginary-order modified Bessel kernel

The registry node below formalizes admitted claim 236. Since mathlib has no named
modified Bessel `K` function, `K_{iτ}(β)` is written using its standard integral
normalization on the positive real axis.
-/

open MeasureTheory

namespace MathlibPlus.Open.Analysis.BesselK

/-- For every positive real `β`, every complex zero in the order parameter `τ`
of `K_{iτ}(β)` is real. The integral is
`K_{iτ}(β) = ∫₀^∞ exp (-β cosh t) cosh (i τ t) dt`. -/
def imaginaryOrderZerosReal : Prop :=
  ∀ (β : ℝ), 0 < β → ∀ (τ : ℂ),
    (∫ t : ℝ in Set.Ioi 0,
      Complex.exp (-(β : ℂ) * Complex.cosh (t : ℂ)) *
        Complex.cosh (Complex.I * τ * (t : ℂ))) = 0 →
    τ.im = 0

end MathlibPlus.Open.Analysis.BesselK
