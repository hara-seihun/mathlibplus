import MathlibPlus.Open.Analysis.Claim15323
import MathlibPlus.Open.Analysis.O0313ForcedRootReflection

open Filter MeasureTheory
open scoped BigOperators ENNReal Topology

namespace MathlibPlus.Open.Analysis.BatchO0313Claim15307

noncomputable section

open MathlibPlus.Open.Analysis.Claim15323
open MathlibPlus.Open.Analysis.O0313ForcedRootReflection
open MathlibPlus.Open.NewResearch2.PeriodicZetaFiber

/-- The factor contributed by one zero root in the disk coordinate. -/
noncomputable def zeroRootFactor15307 (q : ℕ) (z : ℂ) : ℂ :=
  (qRadius q : ℂ) * qPhi q z

/-- The singular-inner carrier for the zero-root factor: it is inner, has no
interior finite zeros, and has the singular radial boundary behavior at the
Cayley point 1. -/
def singularInner15307 (q : ℕ) : Prop :=
  innerOnUnitDisk (qPhi q) ∧
    (∀ z : ℂ, z ∈ Metric.ball (0 : ℂ) 1 → qPhi q z ≠ 0) ∧
    Tendsto
      (fun ρ : ℝ => qPhi q (ρ : ℂ))
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℂ))

/-- A zero root contributes `r Phi_q`, rather than a finite-zero Blaschke
factor. Replacing it by the constant `r` preserves the boundary modulus and
changes the center by `r⁻¹ = exp (log(q)/2)`. The same factor, when retained
in the zero-corrected normalization, can only increase the evaluation slack. -/
def claim15307 : Prop :=
  (∀ q : ℕ, 2 ≤ q →
    let L : ℝ := qLog q
    let r : ℝ := qRadius q
    singularInner15307 q ∧
      0 < r ∧
      r = Real.exp (-L / 2) ∧
      qPhi q 0 = (r : ℂ) ∧
      zeroRootFactor15307 q 0 = (r : ℂ) ^ 2 ∧
      (r : ℂ)⁻¹ = (Real.exp (L / 2) : ℂ) ∧
      (∀ C : Polynomial ℂ, ∀ t : ℝ,
        ‖Polynomial.eval
            (zeroRootFactor15307 q (qCriticalPoint t))
            (C * Polynomial.X)‖ =
          ‖Polynomial.eval
            (zeroRootFactor15307 q (qCriticalPoint t))
            (C * Polynomial.C (r : ℂ))‖) ∧
      (∀ C : Polynomial ℂ,
        Polynomial.eval ((r : ℂ) ^ 2)
            (C * Polynomial.C (r : ℂ)) =
          (r : ℂ)⁻¹ *
            Polynomial.eval ((r : ℂ) ^ 2) (C * Polynomial.X))) ∧
  (∀ (q : ℕ) (Interior Exterior : Type*)
    [Fintype Interior] [Fintype Exterior]
    (coefficient : ℂ) (zeroMultiplicity : ℕ)
    (interiorRoots : Interior → ℂ)
    (exteriorRoots : Exterior → ℂ),
    2 ≤ q →
    finiteInnerDividedData q coefficient zeroMultiplicity
      interiorRoots exteriorRoots →
      let Q := outerPolynomial q coefficient zeroMultiplicity
        interiorRoots exteriorRoots
      (∀ k : ℕ, ∀ t : ℝ,
        retainedZeroSingularFactor q k t =
          (zeroRootFactor15307 q (qCriticalPoint t) /
            (qRadius q : ℂ) ^ 2) ^ k) ∧
      (∀ k : ℕ,
        zeroCorrectedEvaluationSlack q Q ≤
          retainedZeroEvaluationSlack q Q k))

end

end MathlibPlus.Open.Analysis.BatchO0313Claim15307
