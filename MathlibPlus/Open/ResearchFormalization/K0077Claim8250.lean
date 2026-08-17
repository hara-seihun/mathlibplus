import MathlibPlus.Open.NumberTheory.Claim8251

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.K0077Claim8250

open MathlibPlus.Open.NumberTheory.Claim8251

/-- The exact restricted index set `N>1` with `q` absent from `N`. -/
abbrev OuterPrimePowerIndex (q : ℕ) :=
  {N : ℕ // 1 < N ∧ ¬q ∣ N}

/-- The summand on the source's restricted outer index set. -/
noncomputable def restrictedOuterSummand (q a : ℕ) (s : ℝ)
    (N : OuterPrimePowerIndex q) : ℂ :=
  (Complex.ofReal (ArithmeticFunction.moebius N.1 : ℝ)) *
      Complex.ofReal (residueTerm N.1 (q ^ a) : ℝ) /
    Complex.ofReal (Real.rpow (N.1 : ℝ) s)

/-- The restricted-index form of the outer prime-power packet. -/
noncomputable def restrictedOuterPacket (q a : ℕ) (s : ℝ) : ℂ :=
  ∑' N : OuterPrimePowerIndex q, restrictedOuterSummand q a s N

/-- Claim 8250: for a prime base and positive exponent, the outer packet at
`1+t` is exactly the displayed Möbius/residue series over the stated proper
nonmultiples of `q`, with no endpoint or local-factor substitution. -/
def claim8250 : Prop :=
  ∀ (q a : ℕ) (t : ℝ), q.Prime → 1 ≤ a →
    outerPrimePowerResiduePacket q a (1 + t) =
      restrictedOuterPacket q a (1 + t)

end MathlibPlus.Open.ResearchFormalization.K0077Claim8250
