import Mathlib

open Filter Asymptotics Topology
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.C0184ProfileBasics

noncomputable section

/-- The real-parameter polynomial profile `P_L` in the C-0184 statement. -/
def growingProfilePolynomial
    (d : ℝ → ℕ) (a : ℝ → ℕ → ℝ) (L : ℝ) : Polynomial ℝ :=
  1 + ∑ j ∈ Finset.range (d L),
    Polynomial.C (a L (j + 1)) * Polynomial.X ^ (j + 1)

/-- Claim 2731: the growing-degree profile and its coefficient-root bound. -/
def growingDegreeProfileAndCoefficientRootBound_claim2731
    (d : ℝ → ℕ) (a : ℝ → ℕ → ℝ) (B : ℝ → ℝ) : Prop :=
  ∀ L : ℝ,
    1 ≤ B L ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ d L →
        |a L j| ≤ B L ^ j)

/-- Claim 2732: the real-parameter phase-capacity conditions. -/
def phaseCapacityAdmissibility_claim2732
    (k : ℕ) (d : ℝ → ℕ) (B : ℝ → ℝ) : Prop :=
  1 ≤ k ∧
    (∀ L : ℝ, 1 ≤ B L) ∧
    Tendsto
      (fun L : ℝ => B L ^ k * (d L : ℝ) / L)
      atTop (𝓝 0) ∧
    IsLittleO atTop
      (fun L : ℝ => (d L : ℝ) * Real.log (B L))
      (fun L : ℝ => L)

end

end MathlibPlus.Open.ResearchFormalization.C0184ProfileBasics
