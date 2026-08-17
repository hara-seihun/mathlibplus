import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0860ThreeStateSplitJetClaim25383

noncomputable section

/-- The factorial-normalized beta split on the shifted bivariate polynomial
carrier. -/
noncomputable def betaSplit25383
    (P : Polynomial (Polynomial ℚ)) : Polynomial ℚ :=
  ∑ a ∈ P.support, ∑ b ∈ (P.coeff a).support,
    Polynomial.monomial (a + b + 1)
      ((P.coeff a).coeff b * (Nat.factorial a : ℚ) *
        (Nat.factorial b : ℚ) / (Nat.factorial (a + b + 1) : ℚ))

/-- Differentiation in the first input variable. -/
noncomputable def derivativeX25383
    (P : Polynomial (Polynomial ℚ)) : Polynomial (Polynomial ℚ) :=
  P.derivative

/-- Differentiation in the second input variable. -/
noncomputable def derivativeY25383
    (P : Polynomial (Polynomial ℚ)) : Polynomial (Polynomial ℚ) :=
  ∑ a ∈ P.support, Polynomial.monomial a (P.coeff a).derivative

/-- The two endpoint channels. -/
def endpointLeft25383
    (P : Polynomial (Polynomial ℚ)) : Polynomial ℚ :=
  P.coeff 0

noncomputable def endpointRight25383
    (P : Polynomial (Polynomial ℚ)) : Polynomial ℚ :=
  ∑ a ∈ P.support,
    Polynomial.monomial a ((P.coeff a).coeff 0)

/-- Claim 25383: the bulk split and the two endpoint channels are closed
under the left/right face derivatives, with no channel beyond these three. -/
def claim25383 : Prop :=
  (∀ P : Polynomial (Polynomial ℚ),
    (betaSplit25383 P).derivative =
      betaSplit25383 (derivativeX25383 P) + endpointLeft25383 P) ∧
  (∀ P : Polynomial (Polynomial ℚ),
    (betaSplit25383 P).derivative =
      betaSplit25383 (derivativeY25383 P) + endpointRight25383 P) ∧
  (∀ P : Polynomial (Polynomial ℚ),
    (endpointLeft25383 P).derivative =
        endpointLeft25383 (derivativeY25383 P) ∧
      (endpointRight25383 P).derivative =
        endpointRight25383 (derivativeX25383 P))

end

end MathlibPlus.Open.ResearchFormalization.R0860ThreeStateSplitJetClaim25383
