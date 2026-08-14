import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis

def nontrivialZetaZeroThrough (T : ℝ) (z : ℂ) : Prop :=
  riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ T

def claim1041 : Prop :=
  let T₀ : ℝ := 3000175332800
  let X : ℝ := 6000000185827
  let y₀ : ℝ := (1 : ℝ) / 10
  (∀ z : ℂ, nontrivialZetaZeroThrough T₀ z → z.re = (1 : ℝ) / 2) ∧
    T₀ - X / 2 = (1752398865 : ℝ) / 10 ∧
    T₀ - (X + 1) / 2 = 175239886 ∧
    (1 + y₀) / 2 = (55 : ℝ) / 100 ∧
    (55 : ℝ) / 100 > (1 : ℝ) / 2

end MathlibPlus.Open.Analysis
