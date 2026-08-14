import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable def firstThetaShell (u : ℝ) : ℝ :=
  let y := Real.pi * Real.exp (2 * u)
  2 * Real.rpow Real.pi (-1 / 4 : ℝ) * Real.rpow y (5 / 4 : ℝ) *
      (2 * y - 3) * Real.exp (-y)

def first_completed_theta_shell : Prop :=
  ∀ u : ℝ,
    firstThetaShell u =
      let y := Real.pi * Real.exp (2 * u)
      2 * Real.rpow Real.pi (-1 / 4 : ℝ) * Real.rpow y (5 / 4 : ℝ) *
        (2 * y - 3) * Real.exp (-y)

noncomputable def firstThetaWronskian (s : ℕ) (u : ℝ) : ℝ :=
  Matrix.det (fun i j : Fin s =>
    (deriv^[2 * i.1 + j.1]) firstThetaShell u)

def exact_first_shell_wronskian_factorization : Prop :=
  ∀ s : ℕ, 0 < s →
    ∃ (E : ℝ → ℝ) (P : Polynomial ℤ),
      (∀ y : ℝ, 0 < y → 0 < E y) ∧
      P.natDegree = s * (s + 1) / 2 ∧
      ∀ u : ℝ,
        let y := Real.pi * Real.exp (2 * u)
        firstThetaWronskian s u =
          E y * Real.rpow y ((s * (s - 1) / 2 : ℕ) : ℝ) *
            Polynomial.eval₂ (Int.castRingHom ℝ) y P

def rank_ten_strict_extended_chebyshev_chamber : Prop :=
  ∀ r : ℕ, (hr₂ : 2 ≤ r) → r ≤ 10 →
    ∀ u : Fin r → ℝ, StrictMono u →
      Real.pi * Real.exp
          (2 * u ⟨0, Nat.lt_of_lt_of_le (by decide) hr₂⟩) ≥
        2 * (r : ℝ) - 1 →
      0 < Matrix.det (fun i j : Fin r =>
        (deriv^[2 * i.1]) firstThetaShell (u j))

end MathlibPlus.Open.Analysis
