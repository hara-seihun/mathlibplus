import Mathlib

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Analysis.Claim3381

noncomputable def lambertW₀ (x : ℝ) : ℝ :=
  sInf {z : ℝ | 0 ≤ z ∧ z * Real.exp z = x}

noncomputable def primitiveCompletedTheta (u : ℝ) : ℝ :=
  ∑' q : {q : ℕ // 1 ≤ q},
    Real.exp (-Real.pi * (((q : ℕ) : ℝ) ^ 2) * Real.exp (2 * u))

noncomputable def primitiveCompletedThetaMoment (n : ℕ) : ℝ :=
  (2 : ℝ) / (Nat.factorial (2 * n) : ℝ) *
    ∫ u in Set.Ioi (0 : ℝ),
      Real.exp (u / 2) * primitiveCompletedTheta u * u ^ (2 * n)

noncomputable def D (m n : ℕ) : ℝ :=
  if m = 0 then 1 else
    Matrix.det (fun i j : Fin m =>
      primitiveCompletedThetaMoment (n - (i : ℕ) + (j : ℕ)))

noncomputable def w (n : ℕ) : ℝ := lambertW₀ ((2 : ℝ) * n / Real.pi)

noncomputable def gamma (n : ℕ) : ℝ := w n / (1 + w n)

noncomputable def secondDifference (g : ℕ → ℝ) (n : ℕ) : ℝ :=
  g (n + 1) - 2 * g n + g (n - 1)

noncomputable def L (m n : ℕ) : ℝ :=
  Real.log (D m n ^ 2 / (D m (n - 1) * D m (n + 1)))

def lambertVariablesAndDeterminantLogCurvature : Prop :=
  (∀ n : ℕ, w n = lambertW₀ ((2 : ℝ) * n / Real.pi) ∧
    gamma n = w n / (1 + w n)) ∧
  ∀ m n : ℕ,
    0 < D m (n - 1) → 0 < D m n → 0 < D m (n + 1) →
    L m n = -secondDifference (fun k => Real.log (D m k)) n

end MathlibPlus.Open.Analysis.Claim3381
