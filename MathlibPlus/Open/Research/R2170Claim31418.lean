import MathlibPlus.Open.Research.R2170ProjectiveCube

open scoped BigOperators
open Classical
noncomputable section

namespace MathlibPlus.Open.Research.R2170

/-- Claim 31418: extremizers, symmetrization, fixed-face restriction, and a
 diagonal finite-simplex subsequence produce a cube-exchangeable projective law. -/
def claim31418_extremizersProduceExchangeableProjectiveLaw : Prop :=
  ∃ (G : ∀ n : PositiveCubeDimension, SimpleGraph (CubeVertex n.1)),
    (∀ n : PositiveCubeDimension,
      literalC4Free n.1 (G n) ∧
        (edgeCount (G n) : ℝ) = cubeExtremal n.1) ∧
    (∀ n : PositiveCubeDimension,
      finiteProbabilityLaw (symmetrizedMass n.1 (G n)) ∧
        (∀ H : SimpleGraph (CubeVertex n.1),
          symmetrizedMass n.1 (G n) H ≠ 0 → literalC4Free n.1 H) ∧
        symmetrizedRelativeDensity n.1 (G n) = alpha n) ∧
    ∃ (s : ℕ → PositiveCubeDimension)
      (ν : ∀ m : ℕ, SimpleGraph (CubeVertex m) → ℝ),
      StrictMono s ∧
      Filter.Tendsto (fun k : ℕ => (s k).1) Filter.atTop Filter.atTop ∧
      (∀ m : ℕ, ∀ k : ℕ, m ≤ (s k).1 →
        coordinateFace (canonicalFace m (s k).1)) ∧
      (∀ m : ℕ, ∀ n : PositiveCubeDimension, m ≤ n.1 →
        finiteProbabilityLaw (restrictedSymmetrizedMass m n.1 (G n)) ∧
        (∀ H : SimpleGraph (CubeVertex m),
          restrictedSymmetrizedMass m n.1 (G n) H ≠ 0 →
            literalC4Free m H)) ∧
      cubeExchangeableProjectiveLaw ν ∧
      hasCommonDensity ν alphaInfinity ∧
      ∀ m : ℕ, ∀ H : SimpleGraph (CubeVertex m),
        Filter.Tendsto
          (fun k : ℕ => restrictedSymmetrizedMass m (s k).1
            (G (s k)) H)
          Filter.atTop (nhds (ν m H))

end MathlibPlus.Open.Research.R2170
