import Mathlib

namespace MathlibPlus.Analysis.Claim10894

open scoped ComplexConjugate

/-- Claim 10894: the modulus-curvature product identity, with the displayed
quantity retained locally so no source-specific carrier is invented. -/
def product_modulus_curvature : Prop :=
  ∀ (g h g' h' g'' h'' : ℂ),
    let D : ℂ → ℂ → ℂ → ℝ :=
      fun f f' f'' => ‖f'‖ ^ 2 - (f'' * star f).re
    D (g * h) (g' * h + g * h')
        (g'' * h + 2 * g' * h' + g * h'') =
      ‖h‖ ^ 2 * D g g' g'' +
        ‖g‖ ^ 2 * D h h' h'' +
          4 * (g' * star g).im * (h' * star h).im

end MathlibPlus.Analysis.Claim10894
