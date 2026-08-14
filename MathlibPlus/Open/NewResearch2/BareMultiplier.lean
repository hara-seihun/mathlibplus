import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.R0206

private noncomputable def bareJensen18809 (L q w : ℝ) : ℝ :=
  1 + q + q * L ^ 2 * w + (q * L ^ 4 / 24) * w ^ 2

private def bareJensenHyperbolic18809 (L q : ℝ) : Prop :=
  ∃ r s : ℝ, ∀ w : ℝ,
    bareJensen18809 L q w =
      (q * L ^ 4 / 24) * (w - r) * (w - s)

/-- Claim 18805: the squared-variable multiplier is the even entire series
shown in the packet. -/
def claim18805_bareCounterfeitMultiplierSquared : Prop :=
  ∀ (q L : ℝ) (w : ℂ),
    1 + (q : ℂ) * Complex.cosh ((L : ℂ) * Complex.sqrt w) =
      1 + (q : ℂ) +
        ∑' n : ℕ,
          (q : ℂ) * (L : ℂ) ^ (2 * (n + 1)) /
            (Nat.factorial (2 * (n + 1)) : ℂ) * w ^ (n + 1)

/-- Claim 18806: the displayed coefficients of the bare multiplier. -/
def claim18806_bareMultiplierCoefficients : Prop :=
  ∀ (q L : ℝ),
    (let b : ℕ → ℂ := fun n ↦
      if n = 0 then (1 + q : ℂ)
      else (q : ℂ) * (L : ℂ) ^ (2 * n) /
        (Nat.factorial (2 * n) : ℂ)
     b 0 = (1 + q : ℂ) ∧
       ∀ n : ℕ, 1 ≤ n →
         b n = (q : ℂ) * (L : ℂ) ^ (2 * n) /
           (Nat.factorial (2 * n) : ℂ))

/-- Claim 18809: the quadratic Jensen section has the sharp threshold one-fifth,
with a double real root at the threshold and no real factorization below it. -/
def claim18809_sharpHyperbolicityThreshold : Prop :=
  ∀ {q L : ℝ}, 0 < q → L ≠ 0 →
    (bareJensenHyperbolic18809 L q ↔ 1 / 5 ≤ q) ∧
    (q = 1 / 5 →
      ∃ r : ℝ, ∀ w : ℝ,
        bareJensen18809 L q w =
          (q * L ^ 4 / 24) * (w - r) * (w - r)) ∧
    (0 < q ∧ q < 1 / 5 → ¬ bareJensenHyperbolic18809 L q)

/-- Claim 18811: an off-axis zero by itself does not force finite-section
blindness; an explicit base with an off-axis zero can coexist with quadratic
Jensen detection of the bare multiplier. -/
def claim18811_rankEscapeNeedsStrictBase : Prop :=
  ∃ (F : ℂ → ℂ) (L q : ℝ),
    F = (fun z : ℂ ↦ z - 1) ∧ L ≠ 0 ∧ 0 < q ∧ q < 1 / 5 ∧
      (∃ z : ℂ, F z = 0 ∧ z.re ≠ 0) ∧
      ¬ bareJensenHyperbolic18809 L q

private noncomputable def JensenCoefficient18812
    (F : ℂ → ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n F 0 / (Nat.factorial n : ℂ)

private noncomputable def JensenSection18812
    (F : ℂ → ℂ) (r : ℕ) : Polynomial ℂ :=
  Finset.sum (Finset.range (r + 1)) (fun k ↦
    Polynomial.C ((Nat.choose r k : ℂ) * JensenCoefficient18812 F k) *
      Polynomial.X ^ k)

private def realRootedSection18812 (p : Polynomial ℂ) : Prop :=
  ∀ z : ℂ, p.IsRoot z → z.im = 0

/-- Claim 18812: planted-zero location and displacement alone do not give a
base-uniform bound on the first detecting Jensen rank. -/
def claim18812_noBaseUniformRankBound : Prop :=
  ∀ R δ : ℝ, 0 < R → 0 < δ →
    ¬ ∃ D : ℕ, ∀ F : ℂ → ℂ,
      Differentiable ℂ F →
      (∃ z : ℂ, F z = 0 ∧ ‖z‖ = R ∧ |z.re| ≥ δ) →
      ∃ r : ℕ, r ≤ D ∧
        ¬ realRootedSection18812 (JensenSection18812 F r)

end MathlibPlus.Open.NewResearch2.R0206
