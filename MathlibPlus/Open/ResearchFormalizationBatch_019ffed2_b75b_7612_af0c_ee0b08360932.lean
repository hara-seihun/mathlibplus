import Mathlib

open Filter
open scoped Topology

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-- The finite-prime multiplier appearing in the semilocal identification through `c`. -/
noncomputable def semilocalSoninMultiplier (c : ℕ) (t : ℝ) : ℂ :=
  Finset.prod ((Finset.range (c + 1)).filter Nat.Prime) (fun p =>
    (1 - Complex.exp
      (((-(1 : ℂ) / 2) - (t : ℂ) * Complex.I) *
        (Real.log (p : ℝ) : ℂ))))

/-- Its stated finite-prime condition number. -/
noncomputable def semilocalConditionNumber (c : ℕ) : ℝ :=
  Finset.prod ((Finset.range (c + 1)).filter Nat.Prime) (fun p =>
    (1 + (Real.sqrt (p : ℝ))⁻¹) /
      (1 - (Real.sqrt (p : ℝ))⁻¹))

/-- Claim 2407: the displayed conditioning asymptotic and its superpolynomial
consequence, with the finite-prime product made explicit. -/
def claim2407_semilocalSoninMultiplierConditioning : Prop :=
  Tendsto
      (fun c : ℕ =>
        Real.log (semilocalConditionNumber c) /
          (Real.sqrt (c : ℝ) / Real.log (c : ℝ)))
      atTop (𝓝 (4 : ℝ)) ∧
    ∀ d : ℕ,
      Tendsto
        (fun c : ℕ =>
          semilocalConditionNumber c / (c : ℝ) ^ d)
        atTop atTop

/-- Claim 2500: support in an interval strictly to the right of zero preserves
all members of the left-endpoint jet (and therefore any endpoint coefficient
read from that jet). -/
def claim2500_supportSeparationPreservesLeftEndpointJet : Prop :=
  ∀ (a A : ℝ) (k : ℝ → ℝ),
    0 < a →
    a < A →
    Function.support k ⊆ Set.Ioo a A →
    (∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, |x| < ε → k x = 0) ∧
      (∀ n : ℕ, iteratedDeriv n k 0 = 0) ∧
      (∀ (f : ℝ → ℝ),
        ∀ n : ℕ,
          iteratedDeriv n (f + k) 0 = iteratedDeriv n f 0)

end MathlibPlus.Open.ResearchFormalizationBatch
