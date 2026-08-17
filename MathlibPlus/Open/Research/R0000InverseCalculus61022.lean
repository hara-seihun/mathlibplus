import Mathlib

noncomputable section

namespace MathlibPlus.Open.Research.R0000InverseCalculus61022

def qFunction (t x : ℝ) : ℝ :=
  x / (4 * Real.pi) * Real.log (x / (4 * Real.pi)) -
    x / (4 * Real.pi) + 11 / 8 +
      t / 16 * Real.log (x / (4 * Real.pi))

def qPrime (t x : ℝ) : ℝ :=
  Real.log (x / (4 * Real.pi)) / (4 * Real.pi) + t / (16 * x)

def qSecond (t x : ℝ) : ℝ :=
  1 / (4 * Real.pi * x) - t / (16 * x ^ 2)

def qThird (t x : ℝ) : ℝ :=
  -1 / (4 * Real.pi * x ^ 2) + t / (8 * x ^ 3)

/-- Claim 61022: the positive-domain derivatives and exact third derivative of
an inverse branch. -/
def claim61022 : Prop :=
  (∀ (t x : ℝ), 0 < x →
    deriv (qFunction t) x = qPrime t x ∧
      deriv (fun y => deriv (qFunction t) y) x = qSecond t x ∧
        deriv (fun y => deriv (fun z => deriv (qFunction t) z) y) x =
          qThird t x) ∧
    (∀ (t : ℝ) (J : Set ℝ) (y : ℝ) (X : ℝ → ℝ),
      IsOpen J →
        (∃ lo hi : ℝ, lo < hi ∧ J = Set.Ioo lo hi) → y ∈ J →
        ContDiffOn ℝ 3 X J →
          (∀ z ∈ J, 0 < X z ∧ qFunction t (X z) = z) →
            qPrime t (X y) ≠ 0 →
              iteratedDeriv 3 X y =
                (3 * (qSecond t (X y)) ^ 2 -
                    qPrime t (X y) * qThird t (X y)) /
                  (qPrime t (X y)) ^ 5)

end MathlibPlus.Open.Research.R0000InverseCalculus61022

end
