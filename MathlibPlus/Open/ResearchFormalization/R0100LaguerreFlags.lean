import Mathlib
import MathlibPlus.Open.NewResearch2.ModularLaguerre

namespace MathlibPlus.Open.ResearchFormalization.R0100LaguerreFlags

open scoped BigOperators
open MeasureTheory Set

noncomputable section

/-- The positive-particle exponential Laguerre theta mode in Claim 17937. -/
noncomputable def exponentialLaguerreTheta (n : ℕ) (α y : ℝ) : ℝ :=
  ∑' m : ℕ,
    if 0 < m then
      Real.exp (-Real.pi * (m : ℝ) ^ 2 * y) *
        (MathlibPlus.Open.NewResearch2.ModularLaguerre.generalizedLaguerre n α).eval
          (Real.pi * (m : ℝ) ^ 2 * y)
    else 0

/-- The completed zeta factor in Claim 17936. -/
noncomputable def completedZeta (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * riemannZeta s

/-- The rising Pochhammer factorial on complex arguments. -/
noncomputable def pochhammer (z : ℂ) (n : ℕ) : ℂ :=
  ∏ k ∈ Finset.range n, (z + (k : ℂ))

/-- The half-Mellin convention from Claim 17938. -/
noncomputable def halfMellin (A : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ y in Set.Ioi (0 : ℝ),
    (A y : ℂ) * (y : ℂ) ^ (s / 2) / (y : ℂ)

/-- Absolute convergence of the half-Mellin integral on its positive carrier. -/
def halfMellinAbsolutelyConvergent (A : ℝ → ℝ) (s : ℂ) : Prop :=
  IntegrableOn
    (fun y : ℝ => ‖(A y : ℂ) * (y : ℂ) ^ (s / 2) / (y : ℂ)‖)
    (Set.Ioi (0 : ℝ))

/-- Claim 17940: the `α = -1/2` flag, with the half-Mellin equality on the
common absolute-convergence half-plane and the displayed meromorphic
continuation. -/
def halfIntegerMinusLaguerreTransform_claim17940 : Prop :=
  ∀ n : ℕ,
    MeromorphicOn
        (fun s : ℂ =>
          pochhammer ((1 - s) / 2) n / (Nat.factorial n : ℂ) * completedZeta s)
        Set.univ ∧
      ∀ s : ℂ, 1 < s.re →
        halfMellinAbsolutelyConvergent
            (exponentialLaguerreTheta n (-(1 / 2 : ℝ))) s ∧
          halfMellin (exponentialLaguerreTheta n (-(1 / 2 : ℝ))) s =
            pochhammer ((1 - s) / 2) n / (Nat.factorial n : ℂ) * completedZeta s

/-- Claim 17941: the `α = +1/2` flag, with the half-Mellin equality on the
common absolute-convergence half-plane and the displayed meromorphic
continuation. -/
def halfIntegerPlusLaguerreTransform_claim17941 : Prop :=
  ∀ n : ℕ,
    MeromorphicOn
        (fun s : ℂ =>
          pochhammer ((3 - s) / 2) n / (Nat.factorial n : ℂ) * completedZeta s)
        Set.univ ∧
      ∀ s : ℂ, 1 < s.re →
        halfMellinAbsolutelyConvergent
            (exponentialLaguerreTheta n (1 / 2 : ℝ)) s ∧
          halfMellin (exponentialLaguerreTheta n (1 / 2 : ℝ)) s =
            pochhammer ((3 - s) / 2) n / (Nat.factorial n : ℂ) * completedZeta s

end

end MathlibPlus.Open.ResearchFormalization.R0100LaguerreFlags
