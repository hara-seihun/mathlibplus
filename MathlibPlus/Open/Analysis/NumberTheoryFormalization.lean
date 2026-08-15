import Mathlib

noncomputable section

open scoped BigOperators
open Set MeasureTheory

namespace MathlibPlus.Open.Analysis.NumberTheory

/-- Lower incomplete gamma written by its defining integral. -/
def lowerIncompleteGamma (a x : ℝ) : ℝ :=
  ∫ r in Ioc 0 x, r ^ (a - 1) * Real.exp (-r)

/-- The incomplete-gamma window profile. -/
def incompleteGammaWindowProfile (t : ℝ) : ℝ :=
  lowerIncompleteGamma (3 / 2) (Real.exp 2 * t) -
    lowerIncompleteGamma (3 / 2) t

/-- Claim 9340: incomplete-gamma window profile. -/
def incompleteGammaWindowProfileClaim : Prop :=
  ∀ t : ℝ,
    0 < t →
    incompleteGammaWindowProfile t =
      ∫ r in Ioc t (Real.exp 2 * t),
        r ^ ((1 : ℝ) / 2) * Real.exp (-r)

/-- The squarefree-coprime counting function. -/
def squarefreeCoprimeCount (q : ℕ) (y : ℝ) : ℝ :=
  ∑ d ∈ Finset.filter (fun d => Nat.Coprime d q) (Finset.Icc 1 (Nat.floor y)),
    (((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2)

/-- The density in the squarefree-coprime count. -/
def squarefreeCoprimeDensity (q : ℕ) : ℝ :=
  ((riemannZeta (2 : ℂ)).re)⁻¹ *
    ∏ p ∈ q.primeFactors, (p : ℝ) / (p + 1)

/-- Claim 9345: squarefree-coprime density with its q-dependent error term. -/
def squarefreeCoprimeDensityClaim : Prop :=
  ∀ q : ℕ,
    0 < q →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y : ℝ, 1 ≤ y →
        |squarefreeCoprimeCount q y - squarefreeCoprimeDensity q * y| ≤
          C * Real.sqrt y

/-- Claim 9349: Mellin transform of the window profile. -/
def mellinTransformWindowProfileClaim : Prop :=
  ∀ z : ℂ,
    -(3 : ℝ) / 2 < z.re →
    z.re < 0 →
    (∫ t in Ioi 0,
      (incompleteGammaWindowProfile t : ℂ) *
        Complex.exp ((z - 1) * (Real.log t : ℂ))) =
      Complex.Gamma ((3 : ℂ) / 2 + z) *
        (1 - Complex.exp (-2 * z)) / z

end MathlibPlus.Open.Analysis.NumberTheory
