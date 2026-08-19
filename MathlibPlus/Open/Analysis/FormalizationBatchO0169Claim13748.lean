import MathlibPlus.Open.Analysis.FormalizationBatchO0169Claim13744
import MathlibPlus.Open.Research.ExponentialMellinBergmanFormalization_01a00b5c7b35

open scoped BigOperators ComplexConjugate ENNReal
open Filter MeasureTheory Set Topology

namespace MathlibPlus.Open.Analysis.FormalizationBatchO0169Claim13748

noncomputable section

open MathlibPlus.Open.Analysis.FormalizationBatchMellin
open MathlibPlus.Open.Analysis.FormalizationBatchMellin13745_13746_13755
open MathlibPlus.Open.Research.ExponentialMellinBergman

/-- The actual change of the hard-cutoff approximant across the unit interval
from an integer scale to the next integer scale. -/
def hardCutoffUnitJump (N : PositiveNat) (t : ℝ) : ℝ :=
  fixedProfileApproximant (compactProfile 0) ((N.1 + 1 : ℕ) : ℝ) t -
    fixedProfileApproximant (compactProfile 0) (N.1 : ℝ) t

/-- The weighted H-norm of that jump, written in the displayed
`L²([1,∞),dt/t²)` carrier. -/
def hardCutoffUnitJumpNorm (N : PositiveNat) : ℝ :=
  Real.sqrt (hNormSq (hardCutoffUnitJump N))

/-- The separate endpoint transfer used at the hard cutoff: one new
Möbius-weighted generator appears on every unit scale interval, and its
weighted H-norm has the stated square-root order. -/
def hardCutoffUnitJumpControl : Prop :=
  (∀ (N : PositiveNat) (t : ℝ),
    hardCutoffUnitJump N t =
      moebiusReal (N.1 + 1) * gamma (N.1 + 1) t) ∧
    (∀ (n : ℕ), 0 < n →
      hNormSq (gamma n) ≤ 2 / (n : ℝ)) ∧
    (∃ C : ℝ, 0 ≤ C ∧
      ∃ N₀ : ℕ, 0 < N₀ ∧
        ∀ (N : PositiveNat), N₀ ≤ N.1 →
          hardCutoffUnitJumpNorm N ≤ C / Real.sqrt (N.1 : ℝ)) ∧
    (∀ (ρ : ℂ) (W : ℂ → ℂ) (c : ℝ),
      criticalLineSimpleZero ρ →
      profileMellinContinuation (compactProfile 0) W c →
        realErrorLimsup (compactProfile 0) =
            integerErrorLimsup (compactProfile 0) ∧
          (profileLowerBound ρ W ≤ realErrorLimsup (compactProfile 0) ↔
            profileLowerBound ρ W ≤ integerErrorLimsup (compactProfile 0)))

/-- The compact-profile specialization of the real-to-integer transfer used
for every polynomial cutoff with positive degree. -/
def compactProfileStatement7 (m : ℕ) : Prop :=
  (∃ C N₀ : ℝ, 0 ≤ C ∧ 0 < N₀ ∧
    ∀ N : ℝ, N₀ ≤ N →
      ∀ u : ℝ, 0 < u → |u - N| ≤ 1 →
        hDistance
            (fixedProfileApproximant (compactProfile m) u)
            (fixedProfileApproximant (compactProfile m) N) ≤
          ENNReal.ofReal (C / Real.sqrt N)) ∧
    (∀ (ρ : ℂ) (W : ℂ → ℂ) (c : ℝ),
      criticalLineSimpleZero ρ →
      compactProfile m ≠ (fun _ : ℝ => 0) →
      profileMellinContinuation (compactProfile m) W c →
        realErrorLimsup (compactProfile m) =
            integerErrorLimsup (compactProfile m) ∧
          (profileLowerBound ρ W ≤ realErrorLimsup (compactProfile m) ↔
            profileLowerBound ρ W ≤ integerErrorLimsup (compactProfile m)))

/-- Claim 13748: the critical-zero lower bound holds for every compact
profile, with the hard-cutoff and positive-degree integer-transfer mechanisms
kept as the two cases. -/
def claim_13748 : Prop :=
  ∀ (m : ℕ) (ρ : ℂ),
    criticalLineSimpleZero ρ →
      let W := rationalMellin m
      profileLowerBound ρ W ≤ realErrorLimsup (compactProfile m) ∧
        profileLowerBound ρ W ≤ integerErrorLimsup (compactProfile m) ∧
        0 < profileLowerBound ρ W ∧
        (m = 0 ∨ 1 ≤ m) ∧
        (m = 0 → hardCutoffUnitJumpControl) ∧
        (1 ≤ m → compactProfileStatement7 m)

end

end MathlibPlus.Open.Analysis.FormalizationBatchO0169Claim13748
