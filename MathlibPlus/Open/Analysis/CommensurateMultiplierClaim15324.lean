import MathlibPlus.Open.Analysis.Claim15323

open Filter
open scoped Topology

namespace MathlibPlus.Open.Analysis.Claim15324

noncomputable section

open MathlibPlus.Open.Analysis.Claim15323

/-- A varying family of finite commensurate data, with arbitrary finite root
sets at each index and an arbitrary retained zero-root monomial shift. -/
def finiteCorrectedSlackFamily15324 : Prop :=
  ∃ (q : ℕ → ℕ) (slack : ℕ → EReal),
    (∀ j : ℕ, 2 ≤ q j) ∧
      (∀ j : ℕ,
        ∃ (interiorCardinality exteriorCardinality : ℕ)
          (coefficient : ℂ) (zeroMultiplicity : ℕ)
          (interiorRoots : Fin interiorCardinality → ℂ)
          (exteriorRoots : Fin exteriorCardinality → ℂ),
          finiteInnerDividedData (q j) coefficient zeroMultiplicity
              interiorRoots exteriorRoots ∧
            let Q := outerPolynomial (q j) coefficient zeroMultiplicity
              interiorRoots exteriorRoots
            slack j = retainedZeroEvaluationSlack (q j) Q zeroMultiplicity) ∧
      Filter.Tendsto slack Filter.atTop (𝓝 (0 : EReal))

/-- Claim 15324: no family of finite one-frequency multipliers, even with its
integer base, finite degree/root data, coefficients, and monomial shifts all
varying, can drive the fully inner-corrected critical-Cauchy
Hardy/Poisson--Jensen slack to zero. -/
def claim15324 : Prop :=
  ¬ finiteCorrectedSlackFamily15324

end

end MathlibPlus.Open.Analysis.Claim15324
