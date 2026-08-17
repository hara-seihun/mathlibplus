import MathlibPlus.Open.Combinatorics.FixedSupportClaim26067

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0516ComponentProfileStanley26060

noncomputable section

/-- The monomial in the finitely supported profile of component orders.  The
index of `MvPolynomial` is the order variable (the power-sum coordinate). -/
def profileMonomial (p : ℕ →₀ ℕ) : MvPolynomial ℕ ℤ :=
  MvPolynomial.monomial p 1

/-- The coefficient attached to one literal spanning edge state. -/
def stateCoefficient {V : Type*} [Fintype V]
    {G : SimpleGraph V}
    (A : MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.EdgeState G) : ℤ :=
  (-1 : ℤ) ^ A.1.card

/-- The signed sum of profile monomials over all spanning edge states. -/
noncomputable def stateProfileSum {V : Type*} [Fintype V]
    (G : SimpleGraph V) : MvPolynomial ℕ ℤ :=
  letI : Fintype (MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.EdgeState G) :=
    Fintype.ofFinite _
  ∑ A : MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.EdgeState G,
    stateCoefficient A •
      profileMonomial
        (MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.componentProfile
          (MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.stateGraph A))

/-- Claim 26060: the component-profile monomial assignment, the exact
`(-1)^|A|` state coefficients, and Stanley's spanning-state expansion in the
power-sum profile variables. -/
def claim26060 : Prop :=
  (∀ p : ℕ →₀ ℕ,
    profileMonomial p = MvPolynomial.monomial p (1 : ℤ)) ∧
    (∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
      MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.stanleyComponentPolynomial G =
        stateProfileSum G) ∧
    (∀ {V : Type*} [Fintype V]
      {G : SimpleGraph V}
      (A : MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.EdgeState G),
      stateCoefficient A = (-1 : ℤ) ^ A.1.card)

end

end MathlibPlus.Open.ResearchFormalization.R0516ComponentProfileStanley26060
