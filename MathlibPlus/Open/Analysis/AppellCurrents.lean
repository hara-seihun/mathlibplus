import Mathlib

namespace MathlibPlus.Open.Analysis.AppellCurrents

noncomputable section

def gaugedPotential (p γ : ℝ) (a : ℝ → ℝ) : ℝ → ℂ :=
  fun x =>
    ((a x : ℂ) ^ 2 + 2 * ((deriv a x : ℝ) : ℂ) -
        2 * (a x : ℂ) * ((p : ℂ) + Complex.I * (γ : ℂ)) +
        ((p : ℂ) + Complex.I * (γ : ℂ)) ^ 2) / (4 : ℂ)

def hermitianCurrent (y : ℝ → ℂ) (A D : ℝ → ℝ) (B : ℝ → ℂ) : ℝ → ℝ :=
  fun x =>
    A x * Complex.normSq (deriv y x) +
      2 * (B x * deriv y x * star (y x)).re +
      D x * Complex.normSq (y x)

def currentSource (p : ℝ) (a F A : ℝ → ℝ) : ℝ → ℝ :=
  fun x => (p - a x) * F x - deriv A x

def currentCorrection (p : ℝ) (a A : ℝ → ℝ) : ℝ → ℝ :=
  fun x =>
    p ^ 2 * deriv A x - p * A x * deriv a x - 2 * p * a x * deriv A x +
      A x * a x * deriv a x + A x * deriv (deriv a) x +
      (a x) ^ 2 * deriv A x + 2 * deriv A x * deriv a x -
      deriv (deriv (deriv A)) x

namespace Claim12554

def currentDivergenceFormula : Prop :=
  ∀ (p γ : ℝ) (φ a : ℝ → ℝ) (y : ℝ → ℂ)
    (A F D : ℝ → ℝ) (B : ℝ → ℂ),
    γ ≠ 0 →
    (∀ x, a x = deriv φ x) →
    (∀ x, deriv (deriv y) x = gaugedPotential p γ a x * y x) →
    (∀ x,
      B x =
        (((-(deriv A x) : ℝ) : ℂ) +
            Complex.I * ((γ * F x : ℝ) : ℂ)) / (2 : ℂ)) →
    (∀ x, deriv F x = (p - a x) * A x) →
    (∀ x, D x = deriv (deriv A) x / 2 - A x * (gaugedPotential p γ a x).re) →
    ∀ x,
      deriv (hermitianCurrent y A D B) x =
        -((γ ^ 2 * currentSource p a F A x + currentCorrection p a A x) *
            Complex.normSq (y x)) /
          2

end Claim12554

namespace Claim12556

def zeroMeanObstruction : Prop :=
  ∀ (p : ℝ) (φ a A F : ℝ → ℝ),
    (∀ x, a x = deriv φ x) →
    (∀ x, deriv F x = (p - a x) * A x) →
    let S : ℝ → ℝ := currentSource p a F A
    let h : ℝ → ℝ := fun x => Real.exp (-φ x)
    let w_p : ℝ → ℝ := fun x => Real.exp (p * x) * h x
    (Filter.Tendsto (fun x => w_p x * (F x - A x)) Filter.atTop (nhds 0) ∧
        Filter.Tendsto (fun x => w_p x * (F x - A x)) Filter.atBot (nhds 0)) →
      (∫ x : ℝ, w_p x * S x = 0) ∧
        (∀ x, 0 < w_p x) ∧
        (S ≠ (0 : ℝ → ℝ) →
          (∃ x, S x < 0) ∧
            (∃ x, 0 < S x) ∧
            ¬(∀ x, 0 ≤ S x) ∧
            ¬(∀ x, S x ≤ 0))

end Claim12556

end

end MathlibPlus.Open.Analysis.AppellCurrents
