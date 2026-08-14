import Mathlib

namespace MathlibPlus.Open.Analysis.FormalizationBatchEntire

open Filter Set Topology
open scoped BigOperators

noncomputable section


def qPolynomial (B : ℝ) (z : ℂ) : ℂ :=
  (1 - z / ((-B : ℂ) + Complex.I)) *
    (1 - z / ((-B : ℂ) - Complex.I))

def qLinearCoefficient (B : ℝ) : ℝ := 2 * B / (B ^ 2 + 1)
def qQuadraticCoefficient (B : ℝ) : ℝ := 1 / (B ^ 2 + 1)

def claim_13903 : Prop :=
  ∀ M : ℕ, 2 ≤ M →
    let B : ℝ := M + 1
    qPolynomial B = (fun z : ℂ =>
      1 + (qLinearCoefficient B : ℂ) * z +
        (qQuadraticCoefficient B : ℂ) * z ^ 2) ∧
      0 < qLinearCoefficient B ∧ 0 < qQuadraticCoefficient B ∧
      {z : ℂ | qPolynomial B z = 0} =
        ({(-B : ℂ) + Complex.I, (-B : ℂ) - Complex.I} : Set ℂ) ∧
      Real.arctan (1 / B) < 1 / B ∧
      1 / B = 1 / (M + 1 : ℝ) ∧
      1 / (M + 1 : ℝ) < Real.pi / (M + 1 : ℝ)


def dyadic (j : ℕ) : ℝ := Real.rpow 2 (-(j : ℝ))

def finiteK (s : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  Finset.prod (Finset.Icc 1 N) (fun j =>
    (1 : ℂ) + (s * dyadic j : ℂ) * z)

def K (s : ℝ) (z : ℂ) : ℂ :=
  ∏' j : ℕ,
    if 1 ≤ j then (1 : ℂ) + (s * dyadic j : ℂ) * z else 1

def KDeflated (s : ℝ) (q : ℕ) (z : ℂ) : ℂ :=
  ∏' j : ℕ,
    if 1 ≤ j ∧ j ≠ q then (1 : ℂ) + (s * dyadic j : ℂ) * z else 1

def negativeZeroSet (s : ℝ) : Set ℂ :=
  {z : ℂ | ∃ j : ℕ, 1 ≤ j ∧ z = -((2 : ℂ) ^ j) / (s : ℂ)}

def normalized (f : ℂ → ℂ) : Prop := f 0 = 1

def positivePowerSeriesCoefficients (f : ℂ → ℂ) : Prop :=
  ∀ n : ℕ,
    (iteratedDeriv n f 0 / (Nat.factorial n : ℂ)).im = 0 ∧
      0 < (iteratedDeriv n f 0 / (Nat.factorial n : ℂ)).re

def nonPolynomial (f : ℂ → ℂ) : Prop :=
  ¬∃ p : Polynomial ℂ, ∀ z : ℂ, f z = Polynomial.eval z p

def firstCoefficient (f : ℂ → ℂ) : ℝ :=
  (iteratedDeriv 1 f 0 / (Nat.factorial 1 : ℂ)).re

def claim_13904 : Prop :=
  ∀ s : ℝ, 0 < s →
    (Summable (fun j : ℕ => if 1 ≤ j then s * dyadic j else 0) ∧
      (∑' j : ℕ, if 1 ≤ j then s * dyadic j else 0) = s) ∧
    (∀ C : Set ℂ, IsCompact C →
      TendstoUniformlyOn (fun N : ℕ => finiteK s N)
        (K s) atTop C) ∧
    normalized (K s) ∧
    positivePowerSeriesCoefficients (K s) ∧
    Differentiable ℂ (K s) ∧
    nonPolynomial (K s) ∧
    {z : ℂ | K s z = 0} = negativeZeroSet s ∧
    (∀ z : ℂ, z ∈ negativeZeroSet s → deriv (K s) z ≠ 0) ∧
    firstCoefficient (K s) = s


def Fplus (s : ℝ) : ℂ → ℂ := K s

def Fminus (M : ℕ) (s : ℝ) : ℂ → ℂ :=
  fun z => qPolynomial (M + 1) ((s : ℂ) * z) * K s z

def FplusDeflated (s : ℝ) (q : ℕ) : ℂ → ℂ := KDeflated s q

def FminusDeflated (M : ℕ) (s : ℝ) (q : ℕ) : ℂ → ℂ :=
  fun z => qPolynomial (M + 1) ((s : ℂ) * z) * KDeflated s q z

def claim_13905 : Prop :=
  ∀ M : ℕ, 2 ≤ M → ∀ s : ℝ, 0 < s →
    normalized (Fplus s) ∧
      positivePowerSeriesCoefficients (Fplus s) ∧
      Differentiable ℂ (Fplus s) ∧
      nonPolynomial (Fplus s) ∧
      normalized (Fminus M s) ∧
      positivePowerSeriesCoefficients (Fminus M s) ∧
      Differentiable ℂ (Fminus M s) ∧
      nonPolynomial (Fminus M s) ∧
      {z : ℂ | Fplus s z = 0} = negativeZeroSet s ∧
      {z : ℂ | Fminus M s z = 0} =
        negativeZeroSet s ∪
          {((-((M + 1 : ℕ) : ℂ) + Complex.I) / (s : ℂ)),
            ((-((M + 1 : ℕ) : ℂ) - Complex.I) / (s : ℂ))}


def claim_13907 : Prop :=
  ∀ M : ℕ, 2 ≤ M → ∀ s : ℝ, 0 < s →
    firstCoefficient (Fplus s) = s ∧
      firstCoefficient (Fminus M s) =
        s * (1 + 2 * (M + 1 : ℝ) / ((M + 1 : ℝ) ^ 2 + 1)) ∧
      (∀ q : ℕ, 1 ≤ q →
        firstCoefficient (FplusDeflated s q) =
            firstCoefficient (Fplus s) - s * dyadic q ∧
          firstCoefficient (FminusDeflated M s q) =
            firstCoefficient (Fminus M s) - s * dyadic q) ∧
      (∀ η : ℝ, 0 < η → ∃ s : ℝ, 0 < s ∧
        (1 / 4) * firstCoefficient (Fplus s) < min η 1 ∧
        (1 / 4) * firstCoefficient (Fminus M s) < min η 1 ∧
        (∀ q : ℕ, 1 ≤ q →
          (1 / 4) * firstCoefficient (FplusDeflated s q) < min η 1 ∧
          (1 / 4) * firstCoefficient (FminusDeflated M s q) < min η 1))


def evenLift (f : ℂ → ℂ) : ℂ → ℂ := fun w => f (w ^ 2)

def purelyImaginary (z : ℂ) : Prop := z.re = 0
def hasBothNonzeroParts (z : ℂ) : Prop := z.re ≠ 0 ∧ z.im ≠ 0

def claim_13909 : Prop :=
  ∀ M : ℕ, 2 ≤ M → ∀ s : ℝ, 0 < s →
    (∀ w : ℂ, evenLift (Fplus s) w = 0 → purelyImaginary w) ∧
      (∃ w₁ w₂ w₃ w₄ : ℂ,
        w₁ ≠ w₂ ∧ w₁ ≠ w₃ ∧ w₁ ≠ w₄ ∧
          w₂ ≠ w₃ ∧ w₂ ≠ w₄ ∧ w₃ ≠ w₄ ∧
          (w₁ ^ 2 = (-((M + 1 : ℕ) : ℂ) + Complex.I) / (s : ℂ) ∨
            w₁ ^ 2 = (-((M + 1 : ℕ) : ℂ) - Complex.I) / (s : ℂ)) ∧
          (w₂ ^ 2 = (-((M + 1 : ℕ) : ℂ) + Complex.I) / (s : ℂ) ∨
            w₂ ^ 2 = (-((M + 1 : ℕ) : ℂ) - Complex.I) / (s : ℂ)) ∧
          (w₃ ^ 2 = (-((M + 1 : ℕ) : ℂ) + Complex.I) / (s : ℂ) ∨
            w₃ ^ 2 = (-((M + 1 : ℕ) : ℂ) - Complex.I) / (s : ℂ)) ∧
          (w₄ ^ 2 = (-((M + 1 : ℕ) : ℂ) + Complex.I) / (s : ℂ) ∨
            w₄ ^ 2 = (-((M + 1 : ℕ) : ℂ) - Complex.I) / (s : ℂ)) ∧
          (∀ i : Fin 4,
            let w := ![w₁, w₂, w₃, w₄] i
            evenLift (Fminus M s) w = 0 ∧ hasBothNonzeroParts w))

end

end MathlibPlus.Open.Analysis.FormalizationBatchEntire
