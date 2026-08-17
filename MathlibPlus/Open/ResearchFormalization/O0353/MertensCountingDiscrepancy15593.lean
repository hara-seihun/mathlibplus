import Mathlib
import MathlibPlus.Open.ResearchFormalization.O0353Batch

open Filter Set
open scoped BigOperators Topology

namespace MathlibPlus.Open.ResearchFormalization.O0353

noncomputable section

open Classical

/-- The literal zeta prime-power coefficient. -/
noncomputable def literalPrimePowerCoefficient (p k : ℕ) : ℝ :=
  if Nat.Prime p ∧ 0 < k then Real.log (p : ℝ) else 0

/-- The weighted atom at the centered location `k log p`. -/
noncomputable def centeredPrimePowerCumulative
    (Λ : ℕ → ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑' q : ℕ × ℕ,
    if Nat.Prime q.1 ∧ 0 < q.2 ∧
        0 ≤ (q.2 : ℝ) * Real.log (q.1 : ℝ) ∧
        (q.2 : ℝ) * Real.log (q.1 : ℝ) ≤ t then
      Λ q.1 q.2 / (q.1 : ℝ) ^ q.2
    else 0

/-- The centered counting discrepancy, i.e. the mass on `[0,t]` of the
prime-power atoms minus the Lebesgue term, on its stated domain `t ≥ 0`. -/
noncomputable def centeredCountingDiscrepancy
    (Λ : ℕ → ℕ → ℝ) (t : ℝ) : ℝ :=
  if 0 ≤ t then centeredPrimePowerCumulative Λ t - t else 0

/-- The corrected discrepancy for the actual corrected generalized von
Mangoldt coefficients from the O-0353 product. -/
noncomputable def correctedCountingDiscrepancy
    (α τ : ℝ) (Y : ℕ) (u : ℝ) (t : ℝ) : ℝ :=
  centeredCountingDiscrepancy
    (fun p k => correctedLambdaZero α τ Y u p k) t

/-- The exact weighted correction mass
`∑_{p,k}(Λ_Y(p^k)-log p)/p^k`. -/
noncomputable def correctedWeightedMassTerm
    (α τ : ℝ) (Y : ℕ) (u : ℝ) (p k : ℕ) : ℝ :=
  if Nat.Prime p ∧ 0 < k then
    (correctedLambdaZero α τ Y u p k - Real.log (p : ℝ)) /
      (p : ℝ) ^ k
  else 0

noncomputable def correctedWeightedMass
    (α τ : ℝ) (Y : ℕ) (u : ℝ) : ℝ :=
  ∑' q : ℕ × ℕ, correctedWeightedMassTerm α τ Y u q.1 q.2

/-- The exact weighted total variation of the discrete source difference,
written as the absolute prime-power series supplied by Claim 15592. -/
noncomputable def weightedDifferenceTotalVariation
    (α τ : ℝ) (Y : ℕ) (u : ℝ) : ℝ :=
  ∑' q : ℕ × ℕ, |correctedWeightedMassTerm α τ Y u q.1 q.2|

/-- The supremum discrepancy on `t ≥ 0`; the claim separately asserts the
boundedness needed for this conditionally complete supremum to carry its usual
uniform meaning. -/
noncomputable def uniformCountingDiscrepancy
    (α τ : ℝ) (Y : ℕ) (u : ℝ) : ℝ :=
  sSup ((fun t : ℝ =>
    |correctedCountingDiscrepancy α τ Y u t -
      centeredCountingDiscrepancy literalPrimePowerCoefficient t|) ''
      Set.Ici 0)

/-- Claim 15593: the finite correction has exactly zero weighted mass, the
corrected and literal centered counting discrepancies share the Mertens
endpoint `-γ`, and the corrected discrepancy converges uniformly to the
literal one as `Y → ∞`. -/
def claim15593_exactMertensConstantUniformCountingConvergence : Prop :=
  ∀ α τ : ℝ,
    0 < α →
      α < (1 : ℝ) / 2 →
        0 < τ →
          Tendsto
              (centeredCountingDiscrepancy literalPrimePowerCoefficient)
              atTop (nhds (-Real.eulerMascheroniConstant)) ∧
            ∃ (Y₀ : ℕ) (u : ℕ → ℝ),
              (∀ Y : ℕ, Y₀ ≤ Y →
                MathlibPlus.Open.ResearchFormalization.weightedPerturbation
                      α τ Y +
                    MathlibPlus.Open.ResearchFormalization.correctionMass Y
                      (u Y) = 0 ∧
                  correctedWeightedMass α τ Y (u Y) = 0 ∧
                  Summable (fun q : ℕ × ℕ =>
                    |correctedWeightedMassTerm α τ Y (u Y) q.1 q.2|) ∧
                  Tendsto
                    (correctedCountingDiscrepancy α τ Y (u Y))
                    atTop (nhds (-Real.eulerMascheroniConstant)) ∧
                  BddAbove ((fun t : ℝ =>
                    |correctedCountingDiscrepancy α τ Y (u Y) t -
                      centeredCountingDiscrepancy literalPrimePowerCoefficient
                        t|) '' Set.Ici 0)) ∧
              Tendsto
                (fun Y : ℕ => weightedDifferenceTotalVariation α τ Y (u Y))
                atTop (nhds 0) ∧
              Tendsto
                (fun Y : ℕ => uniformCountingDiscrepancy α τ Y (u Y))
                atTop (nhds 0) ∧
              (∀ ε : ℝ, 0 < ε →
                ∃ Y₁ : ℕ, ∀ Y : ℕ, Y₁ ≤ Y →
                  ∀ t : ℝ, 0 ≤ t →
                    |correctedCountingDiscrepancy α τ Y (u Y) t -
                      centeredCountingDiscrepancy literalPrimePowerCoefficient
                        t| < ε)

end

end MathlibPlus.Open.ResearchFormalization.O0353
