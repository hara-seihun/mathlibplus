import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0860BivariateSplit

noncomputable section

open scoped BigOperators

private noncomputable def betaSplit
    (P : Polynomial (Polynomial ℚ)) : Polynomial ℚ :=
  ∑ a ∈ P.support, ∑ b ∈ (P.coeff a).support,
    Polynomial.monomial (a + b + 1)
      ((P.coeff a).coeff b * (Nat.factorial a : ℚ) *
        (Nat.factorial b : ℚ) / (Nat.factorial (a + b + 1) : ℚ))

private noncomputable def derivativeY
    (P : Polynomial (Polynomial ℚ)) : Polynomial (Polynomial ℚ) :=
  ∑ a ∈ P.support, Polynomial.monomial a (P.coeff a).derivative

private def endpointLeft
    (P : Polynomial (Polynomial ℚ)) : Polynomial ℚ :=
  P.coeff 0

private noncomputable def endpointRight
    (P : Polynomial (Polynomial ℚ)) : Polynomial ℚ :=
  ∑ a ∈ P.support,
    Polynomial.monomial a ((P.coeff a).coeff 0)

/-- Claim 25380: the left split commutator is the left endpoint state. -/
def leftSplitFaceCommutator_claim25380 : Prop :=
  ∀ P : Polynomial (Polynomial ℚ),
    (betaSplit P).derivative =
      betaSplit P.derivative + endpointLeft P

/-- Claim 25381: the right split commutator is the right endpoint state. -/
def rightSplitFaceCommutator_claim25381 : Prop :=
  ∀ P : Polynomial (Polynomial ℚ),
    (betaSplit P).derivative =
      betaSplit (derivativeY P) + endpointRight P

/-- Claim 25382: endpoint evaluation propagates through the corresponding
bivariate derivative without creating another local state. -/
def endpointPropagationIdentities_claim25382 : Prop :=
  ∀ P : Polynomial (Polynomial ℚ),
    (endpointLeft P).derivative = endpointLeft (derivativeY P) ∧
      (endpointRight P).derivative = endpointRight P.derivative

end

end MathlibPlus.Open.ResearchFormalization.R0860BivariateSplit
