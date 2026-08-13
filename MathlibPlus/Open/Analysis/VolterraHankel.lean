import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis.VolterraHankel

open scoped BigOperators
open MeasureTheory

private def volterraExpression
    (H : ℝ → ℝ → ℝ) (k : ℕ) (M ω x : ℝ) : ℝ :=
  (1 / 8 : ℝ) *
    ∫ u in Set.Ioi M,
      u * Real.cosh (ω * u) * Real.exp (u / 2) *
        H x (Real.pi * (k : ℝ) * Real.exp u)

private def pairCharacter (x : ℝ) (n m : ℕ) : ℂ :=
  if n = 0 ∨ m = 0 then 0 else
    Complex.exp ((-(x : ℂ)) * Complex.I *
      Complex.log ((n : ℂ) / (m : ℂ)))

private def divisorCharacter (x : ℝ) (k : ℕ) : ℂ :=
  ∑ n ∈ (Finset.Icc 1 k).filter (fun n => n ∣ k),
    pairCharacter x n (k / n)

/-- The moving Volterra product-shell coefficient is the stated integral. -/
def claim13347 (ak : ℝ) (k : ℕ) (M ω x : ℝ)
    (H : ℝ → ℝ → ℝ) : Prop :=
  1 ≤ k → ak = volterraExpression H k M ω x

/-- Absolute convergence permits divisor-character ungrouping. -/
def claim13348 (x : ℝ) (a : ℕ → ℂ) : Prop :=
  Summable (fun k : ℕ =>
      ‖if 1 ≤ k then divisorCharacter x k * a k else 0‖) ∧
    Summable (fun nm : ℕ × ℕ =>
      ‖pairCharacter x nm.1 nm.2 * a (nm.1 * nm.2)‖) ∧
    (∑' k : ℕ, if 1 ≤ k then divisorCharacter x k * a k else 0) =
      ∑' nm : ℕ × ℕ,
        if 1 ≤ nm.1 ∧ 1 ≤ nm.2 then
          pairCharacter x nm.1 nm.2 * a (nm.1 * nm.2)
        else 0

/-- Exact Bessel-profile identity at x=0, with the named K-functions retained. -/
def claim13351 (H₀ K₀ K₁ : ℝ → ℝ) : Prop :=
  ∀ X : ℝ,
    H₀ X = 4 * X ^ 2 *
      ((4 * X ^ 2 + 9) * K₀ (2 * X) - 12 * X * K₁ (2 * X))

/-- Certified positive coefficient intervals at the test parameters. -/
def claim13352 (H₀ : ℝ → ℝ) (a₁ a₂ a₄ : ℝ) : Prop :=
  a₁ = volterraExpression (fun _ X => H₀ X) 1 0 (1 / 4) 0 ∧
    a₂ = volterraExpression (fun _ X => H₀ X) 2 0 (1 / 4) 0 ∧
    a₄ = volterraExpression (fun _ X => H₀ X) 4 0 (1 / 4) 0 ∧
    0 < a₁ ∧ 0 < a₂ ∧ 0 < a₄ ∧
    |a₁ - (0.003740793368185829 : ℝ)| ≤ (4.94 : ℝ) / 10 ^ 19 ∧
    |a₂ - (0.000022102900478574 : ℝ)| ≤ (5.56 : ℝ) / 10 ^ 19 ∧
    |a₄ - ((2.291751137 : ℝ) / 10 ^ 10)| ≤ (7.68 : ℝ) / 10 ^ 20

/-- The first multiplicative Hankel minor is certified strictly negative. -/
def claim13353 (a₁ a₂ a₄ : ℝ) : Prop :=
  0 < a₁ ∧ 0 < a₂ ∧ 0 < a₄ ∧
    |a₁ * a₄ - a₂ ^ 2 - (-(4.87680912820 : ℝ) / 10 ^ 10)| ≤
      (5.47 : ℝ) / 10 ^ 22 ∧
    a₁ * a₄ - a₂ ^ 2 < -(4.8 : ℝ) / 10 ^ 10

/-- The zero-sum quotient test is also strictly negative. -/
def claim13355 (H₀ : ℝ → ℝ) : Prop :=
  let c : ℕ → ℝ := fun i =>
    if i = 1 then 1 else if i = 2 then -100 else if i = 3 then 99 else 0
  let quadratic : ℝ :=
    ∑ i ∈ Finset.Icc 1 3, ∑ j ∈ Finset.Icc 1 3,
      c i * c j * volterraExpression (fun _ X => H₀ X) (i * j) 0 (1 / 4) 0
  (∑ i ∈ Finset.Icc 1 3, c i = 0) ∧
    |quadratic - (-(0.00066196653 : ℝ))| ≤ (5.2 : ℝ) / 10 ^ 12 ∧
    quadratic < -(6.6 : ℝ) / 10 ^ 4

/-- Nicholson's bound makes the entire u>=4 omitted tail negligible. -/
def claim13356 (H₀ : ℝ → ℝ) : Prop :=
  (∀ X : ℝ, 0 < X →
    |H₀ X| ≤ 80 * Real.sqrt Real.pi * Real.rpow X (7 / 2 : ℝ) * Real.exp (-2 * X)) ∧
    (∀ k : ℕ, 1 ≤ k →
      |volterraExpression (fun _ X => H₀ X) k 4 (1 / 4) 0| < (1 : ℝ) / 10 ^ 130)

end MathlibPlus.Open.Analysis.VolterraHankel
