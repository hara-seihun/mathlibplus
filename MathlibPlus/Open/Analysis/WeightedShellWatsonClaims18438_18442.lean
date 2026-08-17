import Mathlib
import MathlibPlus.Analysis.ExponentialRemainder
import MathlibPlus.Open.Analysis.WeightedShellGamma

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

open MeasureTheory

noncomputable section

/-- The shell parameters fixed by the weighted-shell Gamma carrier. -/
def weightedShellA_claim18438 (m : ℕ) : ℝ :=
  Real.pi * (m : ℝ) ^ 2

def weightedShellRho_claim18438 (m : ℕ) : ℝ :=
  2 * weightedShellA_claim18438 m - (1 : ℝ) / 2

def weightedShellNu_claim18438 (j : ℕ) : ℕ :=
  2 * j + 1

def weightedShellRemainder_claim18438 (u : ℝ) : ℝ :=
  Real.exp (2 * u) - 1 - 2 * u

def weightedShellGammaDensity_claim18438 (m j : ℕ) (u : ℝ) : ℝ :=
  let ρ := weightedShellRho_claim18438 m
  let ν := weightedShellNu_claim18438 j
  (ρ ^ ν / (Nat.factorial (ν - 1) : ℝ)) *
    u ^ (ν - 1) * Real.exp (-ρ * u)

/-- The Gamma expectation in the exact shell identity, written by its density. -/
def weightedShellExponentialExpectation_claim18436 (m j : ℕ) : ℝ :=
  let a := weightedShellA_claim18438 m
  ∫ u in Set.Ioi (0 : ℝ),
    Real.exp (-a * weightedShellRemainder_claim18438 u) *
      weightedShellGammaDensity_claim18438 m j u

/-- The shell moment fixed by the exact Gamma expectation identity. -/
def weightedShellMoment_claim18438 (m j : ℕ) : ℝ :=
  let a := weightedShellA_claim18438 m
  let ρ := weightedShellRho_claim18438 m
  let ν := weightedShellNu_claim18438 j
  (2 * Real.exp (-a) / ρ ^ ν) *
    weightedShellExponentialExpectation_claim18436 m j

/-- The first Watson remainder appearing in the two-sided bound. -/
def weightedShellError_claim18438 (m j : ℕ) : ℝ :=
  let a := weightedShellA_claim18438 m
  let ρ := weightedShellRho_claim18438 m
  let ν := weightedShellNu_claim18438 j
  a * (((1 - 2 / ρ)⁻¹) ^ ν - 1 - 2 * (ν : ℝ) / ρ)

/-- Claim 18438: the first two-sided Watson bound. -/
def firstTwoSidedWatsonBound_claim18438 : Prop :=
  ∀ (m j : ℕ),
    1 ≤ m →
      let a := weightedShellA_claim18438 m
      let ρ := weightedShellRho_claim18438 m
      let ν := weightedShellNu_claim18438 j
      let t := weightedShellMoment_claim18438 m j
      let E := weightedShellError_claim18438 m j
      1 - E ≤ t / (2 * Real.exp (-a) / ρ ^ ν) ∧
        t / (2 * Real.exp (-a) / ρ ^ ν) ≤ 1

/-- The finite Gamma moment used by the alternating tower. -/
def weightedShellTowerMoment_claim18440 (m j ell : ℕ) : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ),
    weightedShellRemainder_claim18438 u ^ ell *
      weightedShellGammaDensity_claim18438 m j u

/-- The alternating Taylor tower term `S_L`. -/
def weightedShellTowerSum_claim18440 (m j L : ℕ) : ℝ :=
  let a := weightedShellA_claim18438 m
  ∑ ell ∈ Finset.range (L + 1),
    ((-a) ^ ell / (Nat.factorial ell : ℝ)) *
      weightedShellTowerMoment_claim18440 m j ell

/-- The finite-order condition ensuring the moments through `2K+1` are finite. -/
def weightedShellTowerAdmissible_claim18442 (m j K : ℕ) : Prop :=
  1 ≤ m ∧
    weightedShellRho_claim18438 m >
      2 * ((2 * K + 1 : ℕ) : ℝ)

/-- Claim 18442: the unnormalized alternating-tower enclosure. -/
def unnormalizedIntervalEnclosure_claim18442 : Prop :=
  ∀ (m j K : ℕ),
    weightedShellTowerAdmissible_claim18442 m j K →
      let a := weightedShellA_claim18438 m
      let ρ := weightedShellRho_claim18438 m
      let ν := weightedShellNu_claim18438 j
      let t := weightedShellMoment_claim18438 m j
      let Sodd := weightedShellTowerSum_claim18440 m j (2 * K + 1)
      let Seven := weightedShellTowerSum_claim18440 m j (2 * K)
      (2 * Real.exp (-a) / ρ ^ ν) * Sodd ≤ t ∧
        t ≤ (2 * Real.exp (-a) / ρ ^ ν) * Seven

end

end MathlibPlus.Open.Analysis
