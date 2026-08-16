import Mathlib
import MathlibPlus.Analysis.ReciprocalXi
import MathlibPlus.Open.AnalyticNumberTheory.CompactDistributionMoments

open Set TopologicalSpace Filter MeasureTheory
open scoped BigOperators Distributions Topology
open MathlibPlus.Open.AnalyticNumberTheory.CompactDistributionMoments

namespace MathlibPlus.Open.AnalyticNumberTheory.O0339CompletedShiftClaims

noncomputable section

abbrev ComplexDistribution := Distribution (⊤ : Opens ℝ) ℂ ⊤
abbrev RealTestFunction := TestFunction (⊤ : Opens ℝ) ℝ ⊤

/-- The compact real-line distribution carrier used by both completed-shift
claims. -/
def compactSupportIn (T : ComplexDistribution) (A : ℝ) : Prop :=
  0 ≤ A ∧ IsCompact (Distribution.dsupport T) ∧
    Distribution.dsupport T ⊆ Set.Icc (-A) A

/-- Reality of the complex-valued distribution on real test functions. -/
def isRealDistribution (T : ComplexDistribution) : Prop :=
  ∀ φ : RealTestFunction, (T φ).im = 0

/-- The logarithm of the canonical entire xi carrier at a shifted point. -/
noncomputable def shiftedLogTarget (s : ℂ) (α : ℝ) : ℂ :=
  Complex.log (MathlibPlus.Analysis.ReciprocalXi.xi (s + (α : ℂ)))

/-- The cutoff is required to stay in the zero-free right-half-plane where the
chosen logarithm is smooth. -/
def shiftedPointAdmissible (s : ℂ) (α : ℝ) : Prop :=
  1 < (s + (α : ℂ)).re ∧
    MathlibPlus.Analysis.ReciprocalXi.xi (s + (α : ℂ)) ≠ 0

/-- Canonical completed-shift pairings: test functions agree with the same
log-xi target on an open neighborhood of the actual distributional support,
and the universal clause removes cutoff dependence. -/
def completedShiftPairingValues
    (T : ComplexDistribution) (s : ℂ) : Set ℂ :=
  {w | (∃ (U : Set ℝ) (φre φim : RealTestFunction),
      IsOpen U ∧ Distribution.dsupport T ⊆ U ∧
        (∀ α : ℝ, α ∈ U → shiftedPointAdmissible s α) ∧
        (∀ α : ℝ, α ∈ U →
          (φre α = (shiftedLogTarget s α).re ∧
            φim α = (shiftedLogTarget s α).im)) ∧
        T φre + Complex.I * T φim = w) ∧
    (∀ (U : Set ℝ) (φre φim : RealTestFunction),
      IsOpen U → Distribution.dsupport T ⊆ U →
        (∀ α : ℝ, α ∈ U → shiftedPointAdmissible s α) →
        (∀ α : ℝ, α ∈ U →
          (φre α = (shiftedLogTarget s α).re ∧
            φim α = (shiftedLogTarget s α).im)) →
        T φre + Complex.I * T φim = w)}

/-- The completed shift is tied to the canonical pairing throughout the
right-half-plane tail corresponding to the actual support radius. -/
def completedShiftDefinition
    (T : ComplexDistribution) (A : ℝ) (Y : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, 1 + A < s.re →
    Y s ∈ completedShiftPairingValues T s

/-- Complete monotonicity of a complex function on a real terminal interval,
with the real-valued and alternating-sign clauses explicit. -/
def completelyMonotoneOnTail (F : ℂ → ℂ) : Prop :=
  ∃ σ₀ : ℝ, ∀ σ : ℝ, σ₀ < σ → ∀ n : ℕ,
    (iteratedDeriv n F (σ : ℂ)).im = 0 ∧
      0 ≤ (-1 : ℝ) ^ n * (iteratedDeriv n F (σ : ℂ)).re

/-- A nonnegative, possibly non-finite positive-frequency Laplace
representation, with integrability required for each represented tail value. -/
def nonnegativeLaplaceRepresentation (Y : ℂ → ℂ) : Prop :=
  ∃ (a b : ℝ) (σ₀ : ℝ) (μ : Measure ℝ),
    μ (Set.Iic 0) = 0 ∧
      ∀ σ : ℝ, σ₀ < σ →
        Integrable
            (fun t : ℝ => Complex.exp (-(σ : ℂ) * (t : ℂ)))
            (μ.restrict (Set.Ioi 0)) ∧
        Y (σ : ℂ) = (a : ℂ) + (b : ℂ) * (σ : ℂ) +
          ∫ t : ℝ in Set.Ioi 0,
            Complex.exp (-(σ : ℂ) * (t : ℂ)) ∂μ

/-- Claim 15534: no nonzero real compact completed shift has a completely
monotone second derivative on a terminal interval or an affine plus
nonnegative-frequency Laplace representation. -/
def claim15534 : Prop :=
  ∀ (T : ComplexDistribution) (A : ℝ) (Y : ℂ → ℂ),
    T ≠ 0 → compactSupportIn T A → isRealDistribution T →
      completedShiftDefinition T A Y →
        ¬ completelyMonotoneOnTail (fun s : ℂ => iteratedDeriv 2 Y s) ∧
          ¬ nonnegativeLaplaceRepresentation Y

/-- Real values of the canonical distributional polynomial moments. -/
def realMomentValues
    (T : ComplexDistribution) (j : ℕ) : Set ℝ :=
  {m | (m : ℂ) ∈ compactDistributionMomentValues T j}

/-- A sequence of moment values chosen from the same canonical cutoff
independence relation at every order. -/
def momentSequence (T : ComplexDistribution) (m : ℕ → ℝ) : Prop :=
  ∀ j : ℕ, m j ∈ realMomentValues T j

/-- The first nonzero member of a canonical moment sequence. -/
def firstNonzeroMoment
    (T : ComplexDistribution) (m : ℕ → ℝ) (k : ℕ) : Prop :=
  momentSequence T m ∧ m k ≠ 0 ∧
    ∀ j : ℕ, j < k → m j = 0

/-- Eventual complex big-O semantics along the positive real axis. -/
def complexBigOAtTop (f g : ℝ → ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ σ₀ : ℝ, ∀ σ : ℝ, σ₀ ≤ σ →
    ‖f σ‖ ≤ C * ‖g σ‖

/-- Growth faster than every exponential. -/
def superexponentialGrowth (f : ℝ → ℂ) : Prop :=
  ∀ c : ℝ, 0 ≤ c →
    Tendsto (fun σ : ℝ => ‖f σ‖ / Real.exp (c * σ)) atTop atTop

/-- Decay faster than every exponential. -/
def superexponentialDecay (f : ℝ → ℂ) : Prop :=
  ∀ c : ℝ, 0 ≤ c →
    Tendsto (fun σ : ℝ => ‖f σ‖ * Real.exp (c * σ)) atTop (𝓝 0)

/-- Claim 15536: the first nonzero compact-shift moment gives the exact
three-way Stirling asymptotic trichotomy, including the exponentiated tails. -/
def claim15536 : Prop :=
  ∀ (T : ComplexDistribution) (A : ℝ) (Y : ℂ → ℂ)
    (m : ℕ → ℝ) (k : ℕ),
    T ≠ 0 → compactSupportIn T A → isRealDistribution T →
      completedShiftDefinition T A Y → firstNonzeroMoment T m k →
      (k = 0 →
        Tendsto
            (fun σ : ℝ =>
              Y (σ : ℂ) /
                (((m 0 / 2) * σ * Real.log σ : ℝ) : ℂ))
            atTop (𝓝 1) ∧
          ((0 < m 0 ∧ superexponentialGrowth
                (fun σ : ℝ => Complex.exp (Y (σ : ℂ)))) ∨
            (m 0 < 0 ∧ superexponentialDecay
                (fun σ : ℝ => Complex.exp (Y (σ : ℂ)))))) ∧
      (k = 1 →
        ∃ C : ℂ,
          Tendsto
              (fun σ : ℝ =>
                Y (σ : ℂ) - ((m 1 / 2 : ℝ) : ℂ) * (Real.log σ : ℂ) - C)
              atTop (𝓝 0) ∧
            Tendsto
              (fun σ : ℝ =>
                Complex.exp (Y (σ : ℂ)) /
                  (Complex.exp C *
                    (Real.rpow σ (m 1 / 2) : ℂ)))
              atTop (𝓝 1) ∧ m 1 ≠ 0) ∧
      (2 ≤ k →
        let c : ℂ :=
          (((-1 : ℝ) ^ k * m k) /
            (2 * (k : ℝ) * ((k - 1 : ℕ) : ℝ)) : ℝ)
        c ≠ 0 ∧
          complexBigOAtTop
            (fun σ : ℝ =>
              Y (σ : ℂ) - c * (Real.rpow σ (1 - (k : ℝ)) : ℂ))
            (fun σ : ℝ => (Real.rpow σ (-(k : ℝ)) : ℂ)) ∧
          complexBigOAtTop
            (fun σ : ℝ =>
              Complex.exp (Y (σ : ℂ)) - 1 -
                c * (Real.rpow σ (1 - (k : ℝ)) : ℂ))
            (fun σ : ℝ => (Real.rpow σ (-(k : ℝ)) : ℂ)))

end

end MathlibPlus.Open.AnalyticNumberTheory.O0339CompletedShiftClaims
