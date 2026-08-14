import Mathlib

open scoped BigOperators Classical
open MeasureTheory

namespace MathlibPlus.Open.NewResearch2.R0072

noncomputable section

private def knot (m : ℕ) : ℝ :=
  Real.log (Real.pi * (m : ℝ) ^ 2)

private noncomputable def splineSum (r : ℕ) (s : ℝ) : ℝ :=
  ∑' m : ℕ,
    if 0 < m ∧ knot m ≤ s then
      Real.exp (-knot m / 4) * (s - knot m) ^ r /
        (Nat.factorial r : ℝ)
    else 0

private noncomputable def atomicBirth (φ : ℝ → ℝ) : ℝ :=
  ∑' m : ℕ,
    if 0 < m then Real.exp (-knot m / 4) * φ (knot m) else 0

private noncomputable def partialDirichletSpinor (s ξ : ℝ) : ℝ :=
  ∑' m : ℕ,
    if 0 < m ∧ (m : ℝ) ≤ Real.exp (s / 2) / Real.sqrt Real.pi then
      Real.rpow (m : ℝ) (-(1 / 2 : ℝ) - 2 * ξ)
    else 0

/-- Claim 17692: the arithmetic truncated-power spline field. -/
def claim17692 (A : ℕ → ℝ → ℝ) : Prop :=
  ∀ (r : ℕ) (s : ℝ),
    Set.Finite {m : ℕ | 0 < m ∧ knot m ≤ s} ∧
      A r s = splineSum r s ∧ 0 ≤ A r s

/-- Claim 17693: aggregate moments are weighted spline integrals and recover
 the original even moment sequence. -/
def claim17693
    (A : ℕ → ℝ → ℝ) (M t : ℕ → ℝ) : Prop :=
  (∀ r : ℕ,
    M r = (1 / (2 : ℝ) ^ r) *
      ∫ s in Set.Ioi (knot 1),
        Real.exp (s / 4 - Real.exp s) * A r s) ∧
    (∀ n : ℕ, t n = M (2 * n))

/-- Claim 17694: every spline order has the same positive atomic birth measure,
expressed by its action on smooth compactly supported test functions. -/
def claim17694 (A : ℕ → ℝ → ℝ) : Prop :=
  ∀ (r : ℕ) (φ : ℝ → ℝ),
    ContDiff ℝ (r + 1) φ → HasCompactSupport φ →
      Integrable (fun s => A r s * iteratedDeriv (r + 1) φ s) →
        ((-1 : ℝ) ^ (r + 1)) *
            ∫ s : ℝ, A r s * iteratedDeriv (r + 1) φ s =
          atomicBirth φ

/-- Claim 17695: the exponential generating action spinor packages every
spline order into one field. -/
def claim17695
    (A : ℕ → ℝ → ℝ) (G : ℝ → ℝ → ℝ) : Prop :=
  ∀ (s ξ : ℝ),
    Summable (fun r : ℕ => A r s * ξ ^ r) ∧
      G s ξ = ∑' r : ℕ, A r s * ξ ^ r

/-- Claim 17696: the generating field has the closed partial-Dirichlet-spinor
form with its arithmetic cutoff. -/
def claim17696 (G : ℝ → ℝ → ℝ) : Prop :=
  ∀ (s ξ : ℝ),
    G s ξ =
      Real.exp (ξ * s) *
        Real.rpow Real.pi (-(1 / 4 : ℝ) - ξ) *
          partialDirichletSpinor s ξ

end

end MathlibPlus.Open.NewResearch2.R0072
