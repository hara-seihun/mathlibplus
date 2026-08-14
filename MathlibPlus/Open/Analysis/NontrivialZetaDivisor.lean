import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis

/-- A real, even, compactly supported smooth source satisfying the exact-S0 conditions. -/
def ExactS0Source (q : ℝ → ℝ) : Prop :=
  Function.Even q ∧
    ContDiff ℝ ⊤ q ∧
    HasCompactSupport q ∧
    q 0 = 0 ∧
    (∫ x : ℝ, q x) = 0

/-- The arithmetic sample sum attached to a source. -/
def arithmeticSampleSum (q : ℝ → ℝ) (v : ℝ) : ℝ :=
  ∑' n : ℕ, q (↑(n + 1) * v)

/-- The Mellin completion of the arithmetic sample sum. -/
def sourceCompletion (q : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ v : ℝ in Set.Ioi 0,
    (arithmeticSampleSum q v : ℂ) * Complex.cpow (v : ℂ) (s - 1)

/-- Vanishing of a complex function to order at least `m` at `ρ`. -/
def VanishesToOrderAtLeast (f : ℂ → ℂ) (ρ : ℂ) (m : ℕ) : Prop :=
  ∀ k : ℕ, k < m → iteratedDeriv k f ρ = 0

/-- A nontrivial zero of the Riemann zeta function with its exact multiplicity. -/
def NontrivialZetaZeroOfMultiplicity (ρ : ℂ) (m : ℕ) : Prop :=
  0 < ρ.re ∧
    ρ.re < 1 ∧
    riemannZeta ρ = 0 ∧
    0 < m ∧
    VanishesToOrderAtLeast riemannZeta ρ m ∧
    ¬ VanishesToOrderAtLeast riemannZeta ρ (m + 1)

/-- Every nontrivial zeta zero, with multiplicity, divides every exact-S0 completion. -/
def everyNontrivialZetaZeroDividesEveryCompletion : Prop :=
  ∀ (q : ℝ → ℝ), ExactS0Source q →
    ∀ (ρ : ℂ) (m : ℕ),
      NontrivialZetaZeroOfMultiplicity ρ m →
        VanishesToOrderAtLeast (sourceCompletion q) ρ m

end MathlibPlus.Open.Analysis
