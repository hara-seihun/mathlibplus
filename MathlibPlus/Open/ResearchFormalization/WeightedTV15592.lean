import MathlibPlus.Open.ResearchFormalization.O0353Batch

namespace MathlibPlus.Open.ResearchFormalization

noncomputable section

open Asymptotics Filter MeasureTheory Topology
open scoped BigOperators Classical

/-- The location of the prime-power atom in the centered source. -/
noncomputable def primePowerLocation (p k : ℕ) : ℝ :=
  (k : ℝ) * Real.log (p : ℝ)

/-- The signed weighted difference between the corrected and literal zeta
prime-power coefficients. -/
noncomputable def correctedPrimePowerDifference
    (α τ : ℝ) (Y : ℕ) (u : ℝ) (p k : ℕ) : ℝ :=
  if Nat.Prime p ∧ 0 < k then
    (correctedLambdaZero α τ Y u p k - Real.log (p : ℝ)) /
      (p : ℝ) ^ k
  else 0

/-- A signed measure spec for the discrete part of
`ν_Y - ν_ζ`; the common Lebesgue `-dt` term has canceled. -/
def primePowerDifferenceMeasureSpec
    (ν : SignedMeasure ℝ) (weight : ℕ × ℕ → ℝ) : Prop :=
  ∀ B : Set ℝ, MeasurableSet B →
    ν B =
      ∑' q : ℕ × ℕ,
        if primePowerLocation q.1 q.2 ∈ B then weight q else 0

/-- The total variation norm of the finite signed source difference. -/
noncomputable def primePowerDifferenceTotalVariation
    (ν : SignedMeasure ℝ) : ℝ :=
  (ν.totalVariation).real Set.univ

/-- The explicit weighted discrete term in the total-variation formula. -/
noncomputable def correctedPrimePowerTVTerm
    (α τ : ℝ) (Y : ℕ) (u : ℝ) (p k : ℕ) : ℝ :=
  if Nat.Prime p ∧ 0 < k then
    |correctedLambdaZero α τ Y u p k - Real.log (p : ℝ)| /
      (p : ℝ) ^ k
  else 0

/-- Claim 15592: for one fixed positive quartet parameter pair and the
selected finite corrections, the centered prime-power source difference is
an explicitly atomic signed measure, its total variation is exactly the
weighted prime-power sum, and that norm is `O(Y^(-α))` and tends to zero. -/
def claim15592_weightedTotalVariationConvergence : Prop :=
  ∃ (α τ : ℝ) (u : ℕ → ℝ) (ν : ℕ → SignedMeasure ℝ),
    0 < α ∧ α < (1 : ℝ) / 2 ∧ 0 < τ ∧
      IsBigO atTop
        (fun Y : ℕ => |u Y|)
        (fun Y : ℕ => Real.rpow (Y : ℝ) (-α)) ∧
      (∀ᶠ Y : ℕ in atTop,
        weightedPerturbation α τ Y + correctionMass Y (u Y) = 0) ∧
      (∀ᶠ Y : ℕ in atTop,
        primePowerDifferenceMeasureSpec (ν Y)
          (fun q : ℕ × ℕ =>
            correctedPrimePowerDifference α τ Y (u Y) q.1 q.2)) ∧
      (∀ᶠ Y : ℕ in atTop,
        primePowerDifferenceTotalVariation (ν Y) =
          ∑' q : ℕ × ℕ,
            correctedPrimePowerTVTerm α τ Y (u Y) q.1 q.2) ∧
      IsBigO atTop
        (fun Y : ℕ => primePowerDifferenceTotalVariation (ν Y))
        (fun Y : ℕ => Real.rpow (Y : ℝ) (-α)) ∧
      Tendsto
        (fun Y : ℕ => primePowerDifferenceTotalVariation (ν Y))
        atTop (𝓝 0)

end

end MathlibPlus.Open.ResearchFormalization
