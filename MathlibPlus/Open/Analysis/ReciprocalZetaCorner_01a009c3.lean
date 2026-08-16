import Mathlib

namespace MathlibPlus.Open.Analysis

def reciprocalZetaCornerExpansion : Prop :=
  Asymptotics.IsBigO (nhdsWithin (0 : ℂ) {0}ᶜ)
      (fun w : ℂ =>
        (1 / riemannZeta w) -
          ((-2 : ℂ) + 2 * (Real.log (2 * Real.pi) : ℂ) * w))
      (fun w : ℂ => w ^ 2) ∧
    ∀ p : ℕ, p.Prime →
      Asymptotics.IsBigO (nhdsWithin (0 : ℂ) {0}ᶜ)
        (fun w : ℂ =>
          (1 - Complex.cpow (p : ℂ) (-w)) *
              (1 / (riemannZeta w * (1 - Complex.cpow (p : ℂ) (-w))) - 1) -
            ((-2 : ℂ) +
              (2 * (Real.log (2 * Real.pi) : ℂ) -
                Complex.log (p : ℂ)) * w))
        (fun w : ℂ => w ^ 2)

def localDensityDerivative : Prop :=
  ∀ p : ℕ, p.Prime →
    HasDerivAt
      (fun w : ℂ =>
        1 / (riemannZeta (1 + w) *
          (1 - Complex.cpow (p : ℂ) (-1 - w))))
      ((p : ℂ) / ((p : ℂ) - 1)) 0

end MathlibPlus.Open.Analysis
