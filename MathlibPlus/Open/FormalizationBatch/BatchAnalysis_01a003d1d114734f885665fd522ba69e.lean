import Mathlib

noncomputable section
open scoped BigOperators
open MeasureTheory Set Filter Topology

namespace MathlibPlus.Open.FormalizationBatch.Analysis

/-- The packet's endpoint derivative recurrence, with the polynomial recurrence made explicit. -/
def endpointPacketDerivativeRecurrence : Prop :=
  ∀ (a q s : ℝ),
    ∃ P : ℕ → Polynomial ℝ,
      P 0 = Polynomial.C 1 ∧
        (∀ k : ℕ,
          P (k + 1) =
            (Polynomial.C a - Polynomial.C s * Polynomial.X) * P k +
              Polynomial.C s * Polynomial.X * (P k).derivative) ∧
        (∀ (k : ℕ) (t : ℝ),
          iteratedDeriv k
              (fun t : ℝ => Real.exp (a * t - q * Real.exp (s * t))) t =
            Polynomial.eval (q * Real.exp (s * t)) (P k) *
              Real.exp (a * t - q * Real.exp (s * t)))

/-- Boundary moment rigidity for a finite measure supported on the nonnegative half-line. -/
def boundaryMomentRigidity : Prop :=
  ∀ (μ : Measure ℝ),
    IsFiniteMeasure μ →
      MeasureTheory.Measure.support μ ⊆ Set.Ici 0 →
        (∀ j : ℕ, j ≤ 5 → Integrable (fun x : ℝ => x ^ j) μ) →
          let m : ℕ → ℝ := fun j => ∫ x : ℝ, x ^ j ∂μ
          m 3 * m 5 - (m 4) ^ 2 =
                (1 / 2 : ℝ) *
                  (∫ x : ℝ, ∫ y : ℝ, x ^ 3 * y ^ 3 * (x - y) ^ 2 ∂μ ∂μ) ∧
            0 ≤ m 3 * m 5 - (m 4) ^ 2 ∧
            ((m 3 * m 5 - (m 4) ^ 2 = 0) ↔
              ∃ z : ℝ, 0 ≤ z ∧ MeasureTheory.Measure.support μ ⊆ ({0, z} : Set ℝ))

/-- The rising factorial used for the gamma moments. -/
def risingFactorial (α : ℝ) (j : ℕ) : ℝ :=
  ∏ k ∈ Finset.range j, (α + (k : ℝ))

/-- The gamma law written as a density on the positive half-line. -/
def gammaProbabilityMeasure (α : ℝ) : Measure ℝ :=
  MeasureTheory.Measure.withDensity (volume.restrict (Set.Ioi 0))
    (fun x => ENNReal.ofReal
      (Real.rpow x (α - 1) * Real.exp (-x) / Real.Gamma α))

/-- Gamma moments and strict positivity of all generalized Hankel minors. -/
def gammaMomentsAndStrictGeneralizedHankelTotalPositivity : Prop :=
  ∀ α : ℝ, 0 < α →
    let μ := gammaProbabilityMeasure α
    IsProbabilityMeasure μ ∧
      (∀ j : ℕ, ∫ x : ℝ, x ^ j ∂μ = risingFactorial α j) ∧
      (∀ (n : ℕ), 0 < n →
        ∀ (r c : Fin n → ℕ), StrictMono r → StrictMono c →
          0 < Matrix.det (fun i j => risingFactorial α (r i + c j)))

/-- Shifted gamma cells and the completed even-jet column scaling. -/
def shiftedGammaCellsRealizeMomentMatrix : Prop :=
  ∀ α : ℝ, 0 < α →
    (∀ (p q : ℕ),
      (∫ u in Set.Ioi 0,
          u ^ q *
            (u ^ p * Real.rpow u (α - 1) * Real.exp (-u) / Real.Gamma α)) =
        risingFactorial α (p + q)) ∧
    (∀ (p q : ℕ),
      (1 / (Nat.factorial (2 * q) : ℝ)) *
          (∫ v in Set.Ioi 0,
            v ^ (2 * q) *
              (2 * Real.rpow v (2 * (p : ℝ) + 2 * α - 1) *
                Real.exp (-v ^ 2) / Real.Gamma α)) =
        risingFactorial α (p + q) / (Nat.factorial (2 * q) : ℝ)) ∧
    (∀ (n : ℕ), 0 < n →
      ∀ (r c : Fin n → ℕ), StrictMono r → StrictMono c →
        0 < Matrix.det (fun i j => risingFactorial α (r i + c j)) →
        0 < Matrix.det
          (fun i j =>
            risingFactorial α (r i + c j) /
              (Nat.factorial (2 * c j) : ℝ)))

end MathlibPlus.Open.FormalizationBatch.Analysis
