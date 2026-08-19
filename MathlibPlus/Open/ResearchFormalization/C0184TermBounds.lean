import Mathlib
import MathlibPlus.Open.ResearchFormalization.C0184ProfileBasics
import MathlibPlus.Open.ResearchFormalization.C0184WeightedSource

open Filter MeasureTheory Topology Asymptotics
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.C0184TermBounds

noncomputable section

open MathlibPlus.Open.ResearchFormalization.C0184
open MathlibPlus.Open.ResearchFormalization.C0184ProfileBasics
open MathlibPlus.Open.ResearchFormalization.C0184WeightedSource

/-- The actual `j`-th C-0180 profile correction at real scale `L`. -/
def profileTerm
    (k : ℕ) (α L a : ℝ) (j : ℕ) : ℝ → ℝ :=
  (a / Real.rpow L ((j : ℝ) / (k : ℝ))) •
    ((mathcalZ^[j]) (baselineCarrier α k))

/-- C-0180 equation (4), carried explicitly for the individual term estimate. -/
def weightedSuperheatInput
    (k : ℕ) (α : ℝ) (m : ℕ) (C_m : ℝ) : Prop :=
  ∀ j : ℕ,
    sourceSeminorm
        ((mathcalL^[m]) ((mathcalZ^[j]) (baselineCarrier α k))) ≤
      Real.rpow (C_m * (j + 1 : ℝ))
        ((j : ℝ) / (k : ℝ) + C_m)

/-- Claim 2735: the exact displayed bound controls the coefficient-scaled
`j`-th correction in the fixed C-0180 source seminorm. -/
def individualProfileTermEstimate_claim2735
    (k : ℕ) (α : ℝ) (m : ℕ) (C_m L B a : ℝ) (j : ℕ) : Prop :=
  1 ≤ k ∧ 0 < α ∧ 0 < C_m ∧
    (weightedSuperheatInput k α m C_m →
      (0 < L ∧ 1 ≤ B ∧ 1 ≤ j ∧ |a| ≤ B ^ j →
        sourceSeminorm
            ((mathcalL^[m]) (profileTerm k α L a j)) ≤
          C_m * Real.rpow (j + 1 : ℝ) C_m *
            Real.rpow
              (C_m * B ^ k * (j + 1 : ℝ) / L)
              ((j : ℝ) / (k : ℝ))))

def profiledCarrier
    (k : ℕ) (α : ℝ) (d : ℝ → ℕ)
    (a : ℝ → ℕ → ℝ) (L : ℝ) : ℝ → ℝ :=
  growingProfileCarrier k (baselineCarrier α k) d a L

/-- Claim 2736: under the exact coefficient-root and phase-capacity
conditions, the correction terms (and only the terms `1 ≤ j ≤ d L`) vanish
in every fixed source seminorm. -/
def vanishingSourceCorrection_claim2736
    (k : ℕ) (α : ℝ) (d : ℝ → ℕ) (a : ℝ → ℕ → ℝ)
    (B : ℝ → ℝ) : Prop :=
  1 ≤ k ∧ 0 < α ∧
    growingDegreeProfileAndCoefficientRootBound_claim2731 d a B ∧
    phaseCapacityAdmissibility_claim2732 k d B ∧
    (∀ m : ℕ, ∀ C_m : ℝ,
      0 < C_m → weightedSuperheatInput k α m C_m →
        (Tendsto
          (fun L : ℝ =>
            ∑ j ∈ Finset.Icc 1 (d L),
              C_m * Real.rpow (j + 1 : ℝ) C_m *
                Real.rpow
                  (C_m * B L ^ k * (j + 1 : ℝ) / L)
                  ((j : ℝ) / (k : ℝ)))
          atTop (𝓝 0) ∧
        Tendsto
          (fun L : ℝ =>
            sourceSeminorm
              ((mathcalL^[m])
                (profiledCarrier k α d a L - baselineCarrier α k)))
          atTop (𝓝 0)))

end

end MathlibPlus.Open.ResearchFormalization.C0184TermBounds
