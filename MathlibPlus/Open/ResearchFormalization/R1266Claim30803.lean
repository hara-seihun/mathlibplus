import MathlibPlus.Open.ResearchFormalization.R1266Claim30804

namespace MathlibPlus.Open.ResearchFormalization.R1266Claim30803

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1266Claim30804

/-- The polynomial whose two coefficients occur in the double-star
coefficient identities. -/
def dsDeltaMinusESquare (a b : ℕ) : Polynomial ℚ :=
  dsDelta a b - (dsE a b) ^ 2

/-- Claim 30803: the two displayed coefficients of the double-star
 discriminant collar, in the root-balanced parameter range. -/
def claim30803_coefficientIdentities : Prop :=
  ∀ a b : ℕ, 2 ≤ a → 2 ≤ b → a ≤ 2 * b - 1 →
    (dsDeltaMinusESquare a b).coeff (a - 1) = 4 * (a : ℚ) ∧
      (dsDeltaMinusESquare a b).coeff a =
        4 * ((a : ℚ) ^ 2 + 2 * (a : ℚ) * (b : ℚ) + 1) -
          (if b = 2 then 8 * (a : ℚ) else 0)

end

end MathlibPlus.Open.ResearchFormalization.R1266Claim30803
