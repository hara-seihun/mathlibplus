import Mathlib

open scoped BigOperators Interval
open Filter MeasureTheory Set

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- The configurations with exactly `n` particles. -/
abbrev Configuration (n : ℕ) := {S : Finset ℕ // S.card = n}

/-- The squared support coordinate attached to a site. -/
def supportPoint (z : ℕ → ℕ → ℝ) (n i : ℕ) : ℝ := z n i ^ 2

/-- Positive sites in the strict order `z n i > z n j` for `i < j`. -/
def positiveOrderedSites (z : ℕ → ℕ → ℝ) : Prop :=
  ∀ n i, 0 < z n i ∧ ∀ j, i < j → z n j < z n i

/-- Positive weights attached to the sites. -/
def positiveSiteWeights (ω : ℕ → ℕ → ℝ) : Prop :=
  ∀ n i, 0 < ω n i

/-- The squared-Vandermonde weight of an `n`-particle configuration. -/
def squaredVandermondeWeight
    (z ω : ℕ → ℕ → ℝ) (n : ℕ) (S : Configuration n) : ENNReal :=
  ENNReal.ofReal
    (Finset.prod (S.1) (fun i => ω n i) *
      Finset.prod (S.1) (fun i =>
        Finset.prod (S.1) (fun j =>
          if i < j then (supportPoint z n i - supportPoint z n j) ^ 2 else 1)))

/-- The normalization of the squared-Vandermonde ensemble. -/
def squaredVandermondeNormalization
    (z ω : ℕ → ℕ → ℝ) (n : ℕ) : ENNReal :=
  tsum (fun S : Configuration n => squaredVandermondeWeight z ω n S)

/-- Point-mass form of the normalized squared-Vandermonde law. -/
def hasSquaredVandermondeLaw
    (z ω : ℕ → ℕ → ℝ)
    (P : ∀ n, ProbabilityMeasure (Configuration n)) : Prop :=
  ∀ n S,
    (P n).toMeasure {S} =
      squaredVandermondeWeight z ω n S /
        squaredVandermondeNormalization z ω n

/-- The fixed negative-axis Christoffel factor. -/
def fixedTiltFactor
    (z : ℕ → ℕ → ℝ) (s₀ : ℝ) (n : ℕ) (S : Configuration n) : ENNReal :=
  ENNReal.ofReal (Finset.prod (S.1) (fun i => s₀ + supportPoint z n i))

/-- The expectation of the fixed tilt under the base law. -/
def fixedTiltExpectation
    (z : ℕ → ℕ → ℝ) (s₀ : ℝ)
    (P : ∀ n, ProbabilityMeasure (Configuration n)) (n : ℕ) : ENNReal :=
  ∫⁻ S, fixedTiltFactor z s₀ n S ∂(P n).toMeasure

/-- Point-mass form of the normalized fixed negative-axis tilt. -/
def hasFixedNegativeAxisChristoffelTilt
    (z : ℕ → ℕ → ℝ) (s₀ : ℝ)
    (P Ptilt : ∀ n, ProbabilityMeasure (Configuration n)) : Prop :=
  ∀ n S,
    (Ptilt n).toMeasure {S} =
      fixedTiltFactor z s₀ n S * (P n).toMeasure {S} /
        fixedTiltExpectation z s₀ P n

/-- The particle empirical measure, with the zero-particle case fixed harmlessly. -/
def particleEmpiricalMeasure
    (z : ℕ → ℕ → ℝ) (n : ℕ) (S : Configuration n) : ProbabilityMeasure ℝ := by
  by_cases hn : n = 0
  · refine ⟨Measure.dirac (0 : ℝ), ?_⟩
    constructor
    simp
  · have hcard : 0 < S.1.card := by
      rw [S.2]
      exact Nat.pos_of_ne_zero hn
    have hS : S.1.Nonempty := Finset.card_pos.mp hcard
    letI : Nonempty S.1.attach := by
      rcases hS with ⟨i, hi⟩
      exact ⟨⟨⟨i, hi⟩, by simp⟩⟩
    let p : PMF ℝ :=
      PMF.map (fun i : S.1.attach => z n i.1)
        (PMF.uniformOfFintype S.1.attach)
    exact ⟨p.toMeasure, by infer_instance⟩

/-- The equilibrium density from the arcsine-mixture representation. -/
def equilibriumDensity (x : ℝ) : ℝ :=
  2 * ∫ u in (0 : ℝ)..1,
    if 0 < x ∧ x < (Real.pi / 2) / u then
      1 / (Real.pi * Real.sqrt (((Real.pi / 2) / u) ^ 2 - x ^ 2))
    else 0

/-- A probability measure is the stated `ρ_*(x) dx`. -/
def hasEquilibriumDensity (ρ : ProbabilityMeasure ℝ) : Prop :=
  ∀ A : Set ℝ, MeasurableSet A →
    ρ.toMeasure A =
      ∫⁻ x in A, ENNReal.ofReal (equilibriumDensity x) ∂volume

/--
Speed-`n²` fixed-tilt exponential contiguity: every weak neighborhood of the
arcsine-mixture equilibrium measure has exponentially small complement under
the fixed negative-axis Christoffel tilt.
-/
def speed_n_squared_fixed_tilt_exponential_contiguity
    (z ω : ℕ → ℕ → ℝ)
    (h_sites : positiveOrderedSites z)
    (h_weights : positiveSiteWeights ω)
    (s₀ : ℝ) (hs₀ : 0 < s₀)
    (P : ∀ n, ProbabilityMeasure (Configuration n))
    (hP : hasSquaredVandermondeLaw z ω P)
    (Ptilt : ∀ n, ProbabilityMeasure (Configuration n))
    (hPtilt : hasFixedNegativeAxisChristoffelTilt z s₀ P Ptilt)
    (ρ : ProbabilityMeasure ℝ)
    (hρ : hasEquilibriumDensity ρ) : Prop :=
  ∀ U : Set (ProbabilityMeasure ℝ), U ∈ nhds ρ →
    Filter.limsup
      (fun n : ℕ =>
        (((n : EReal)⁻¹) ^ 2) *
          ENNReal.log
            ((Ptilt n).toMeasure
              {S | particleEmpiricalMeasure z n S ∉ U}))
      atTop < 0

end
end MathlibPlus.Open.Analysis
