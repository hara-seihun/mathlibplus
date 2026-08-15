import Mathlib

open scoped BigOperators Topology
open Set Filter MeasureTheory

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- The `n`-particle configurations selected from the ordered sites. -/
def Configuration (n : ℕ) := {S : Finset ℕ // S.card = n}

instance configurationMeasurableSpace (n : ℕ) : MeasurableSpace (Configuration n) := ⊤

def configurationSet {n : ℕ} (S : Configuration n) : Finset ℕ := S.val

/-- The squared-Vandermonde weight of a configuration. -/
def ensembleWeight (z ω : ℕ → ℕ → ℝ) (n : ℕ) (S : Configuration n) : ℝ :=
  (∏ i ∈ configurationSet S, ω n i) *
    ∏ i ∈ configurationSet S, ∏ j ∈ (configurationSet S).filter (fun j => i < j),
      (z n i ^ 2 - z n j ^ 2) ^ 2

/-- Normalization of a real density against counting measure. -/
def normalizedDensity {α : Type*} [MeasurableSpace α] (w : α → ℝ) : Measure α :=
  ((ENNReal.ofReal (∫ x, w x ∂Measure.count))⁻¹) •
    Measure.count.withDensity (fun x => ENNReal.ofReal (w x))

/-- The base squared-Vandermonde ensemble. -/
def baseEnsemble (z ω : ℕ → ℕ → ℝ) (n : ℕ) : Measure (Configuration n) :=
  normalizedDensity (ensembleWeight z ω n)

/-- The discrete orthogonality measure on the squared sites. -/
def supportMeasure (z ω : ℕ → ℕ → ℝ) (n : ℕ) : Measure ℝ :=
  Measure.sum (fun i =>
    ENNReal.ofReal (ω n i) • Measure.dirac (z n i ^ 2))

/-- The empirical measure of a configuration of `n` particles. -/
def particleEmpiricalMeasure (z : ℕ → ℕ → ℝ) (n : ℕ)
    (S : Configuration n) : Measure ℝ :=
  ENNReal.ofReal ((n : ℝ)⁻¹) • ∑ i ∈ configurationSet S, Measure.dirac (z n i)

/-- The Christoffel factor used to tilt the negative-axis ensemble. -/
def christoffelFactor (z : ℕ → ℕ → ℝ) (s₀ : ℝ) (n : ℕ)
    (S : Configuration n) : ℝ :=
  ∏ i ∈ configurationSet S, (s₀ + z n i ^ 2)

/-- The fixed negative-axis Christoffel tilt of the base ensemble. -/
def fixedTilt (z ω : ℕ → ℕ → ℝ) (s₀ : ℝ) (n : ℕ) : Measure (Configuration n) :=
  let P := baseEnsemble z ω n
  let c := christoffelFactor z s₀ n
  ((ENNReal.ofReal (∫ S, c S ∂P))⁻¹) •
    P.withDensity (fun S => ENNReal.ofReal (c S))

/-- The equilibrium density supplied by the arcsine-mixture formula. -/
def rhoStar (z : ℝ) : ℝ :=
  2 * ∫ u in Set.Icc (0 : ℝ) 1,
    if 0 < z ∧ z < (Real.pi / 2) / u then
      1 / (Real.pi * Real.sqrt (((Real.pi / 2) / u) ^ 2 - z ^ 2))
    else 0

/-- The measure `ρ_*(z) dz` on the nonnegative half-line. -/
def rhoStarMeasure : Measure ℝ :=
  (MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))).withDensity
    (fun z => ENNReal.ofReal (rhoStar z))

/-- A basic weak neighborhood, written using bounded continuous test functions. -/
def weakNeighborhood (ν : Measure ℝ) (U : Set (Measure ℝ)) : Prop :=
  ν ∈ U ∧
    ∃ k : ℕ, ∃ f : Fin k → BoundedContinuousFunction ℝ ℝ,
      ∃ ε : Fin k → ℝ,
        (∀ j, 0 < ε j) ∧
          {μ : Measure ℝ |
              ∀ j, |(∫ x, f j x ∂μ) - (∫ x, f j x ∂ν)| < ε j} ⊆ U

/-- Speed-`n²` exponential concentration of the fixed tilt at `ν`. -/
def speedNSqConcentration (z ω : ℕ → ℕ → ℝ) (s₀ : ℝ)
    (ν : Measure ℝ) : Prop :=
  ∀ U : Set (Measure ℝ), weakNeighborhood ν U →
    Filter.limsup
        (fun n : ℕ =>
          ((n : ℝ) ^ 2)⁻¹ *
            Real.log
              (ENNReal.toReal
                ((fixedTilt z ω s₀ n)
                  {S : Configuration n |
                    particleEmpiricalMeasure z n S ∉ U})))
      atTop < 0

/--
Speed-`n²` concentration of the fixed tilt forces the speed-`n` potential.
The antecedent records the ordered positive sites, positive weights, the
monic orthogonal-polynomial carrier, the discrete Heine identity, negative-
axis positivity, and concentration of every fixed tilt.
-/
def speed_n_sq_concentration_forces_speed_n_potential
    (z ω : ℕ → ℕ → ℝ) (p : ℕ → Polynomial ℝ) : Prop :=
  ( (∀ n i, 0 < z n i ∧ z n (i + 1) < z n i) ∧
    (∀ n i, 0 < ω n i) ∧
    (∀ n, MeasureTheory.IsProbabilityMeasure (baseEnsemble z ω n)) ∧
    (∀ s₀, 0 < s₀ → ∀ n,
      MeasureTheory.IsProbabilityMeasure (fixedTilt z ω s₀ n)) ∧
    (∀ n,
      (p n).Monic ∧
      (p n).natDegree = n ∧
      (∀ q : Polynomial ℝ, q.natDegree < n →
        ∫ x, Polynomial.eval x (p n) * Polynomial.eval x q
          ∂supportMeasure z ω n = 0)) ∧
    (∀ n x,
      Polynomial.eval x (p n) =
        ∫ S, ∏ i ∈ configurationSet S, (x - z n i ^ 2)
          ∂baseEnsemble z ω n) ∧
    (∀ n s, 0 < s →
      0 < (-1 : ℝ) ^ n * Polynomial.eval (-s) (p n)) ∧
    (∀ s₀, 0 < s₀ →
      speedNSqConcentration z ω s₀ rhoStarMeasure) ) →
  ∀ s s₀, 0 < s → 0 < s₀ →
    Tendsto
      (fun n : ℕ =>
        ((n : ℝ)⁻¹) *
          Real.log
            (Polynomial.eval (-s) (p n) /
              Polynomial.eval (-s₀) (p n)))
      atTop
      (𝓝 (∫ z in Set.Ici (0 : ℝ),
        Real.log ((s + z ^ 2) / (s₀ + z ^ 2)) * rhoStar z))

end
end MathlibPlus.Open.Analysis
