import Mathlib

namespace MathlibPlus.Open.Research

open scoped BigOperators

noncomputable section

/-- The compact-window factors used by the reset argument. -/
def resetV (S x : ℝ) : ℝ :=
  (2 / S) * Set.indicator (Set.Icc (-S / 4) (S / 4)) (fun _ => (1 : ℝ)) x

def resetB (S : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  (2 * (m : ℝ) / S) *
    Set.indicator
      (Set.Icc (-S / (4 * (m : ℝ))) (S / (4 * (m : ℝ))))
      (fun _ => (1 : ℝ)) x

def resetConvolution (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y : ℝ, f y * g (x - y)

def resetConvolutionPower (f : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun x => if x = 0 then 1 else 0
  | 1 => f
  | n + 2 => fun x =>
      resetConvolution (resetConvolutionPower f (n + 1)) f x

def resetWindowCount (L S : ℝ) : ℕ :=
  Int.toNat (Int.floor (L * S / 4))

def resetOmegaDensity (u v L : ℝ) (x : ℝ) : ℝ :=
  let S := v - u
  let c := (u + v) / 2
  let m := resetWindowCount L S
  resetConvolution (resetV S)
    (resetConvolutionPower (resetB S m) m) (x - c)

def resetOmegaMean (u v L : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ, f x * resetOmegaDensity u v L x

def resetOmegaMass (u v L : ℝ) (E : Set ℝ) : ℝ :=
  ∫ x in E, resetOmegaDensity u v L x

def resetPolynomial {K : ℕ} (S : ℝ) (roots : Fin K → ℝ) (x : ℝ) : ℝ :=
  ∏ j : Fin K, (x - roots j) / S

/-- Admitted logarithmic reset-polynomial mean estimate and intersection conclusion. -/
def claim3582 : Prop :=
  ∀ (u v L : ℝ) (K : ℕ) (roots : Fin K → ℝ) (R : ℝ → ℝ) (a : ℝ),
    u ≤ v →
    0 < v - u →
    8 ≤ L * (v - u) →
    (∀ j : Fin K, roots j ∈ Set.Icc u v) →
    (resetOmegaMass u v L {x : ℝ | |R x| ≥ a} ≥ (3 : ℝ) / 4) →
    (∀ x : ℝ, resetPolynomial (v - u) roots x ≠ 0 →
      -Real.log |resetPolynomial (v - u) roots x| =
        ∑ j : Fin K, Real.log ((v - u) / |x - roots j|)) ∧
    resetOmegaMean u v L
          (fun x => -Real.log |resetPolynomial (v - u) roots x|) ≤
        2 * (1 + Real.log 2) * (K : ℝ) ∧
      resetOmegaMass u v L
          {x : ℝ |
            |R x| ≥ a ∧
              |resetPolynomial (v - u) roots x| ≥
                Real.exp (-4 * (1 + Real.log 2) * (K : ℝ))} ≥
        (1 : ℝ) / 4

end

end MathlibPlus.Open.Research
