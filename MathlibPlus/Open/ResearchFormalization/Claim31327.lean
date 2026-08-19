import MathlibPlus.Open.ResearchFormalization.Claim31331

namespace MathlibPlus.Open.ResearchFormalization.Claim31327

noncomputable section

abbrev ShiftedBoundaryPolynomial :=
  MathlibPlus.Open.ResearchFormalization.Claim31331.ShiftedBoundaryPolynomial

abbrev RootedFiniteTree :=
  MathlibPlus.Open.RootedTreeBoundary.RootedFiniteTree

abbrev shiftedBoundaryD
    (R : RootedFiniteTree) : ShiftedBoundaryPolynomial :=
  MathlibPlus.Open.ResearchFormalization.Claim31331.shiftedBoundaryD R

abbrev rootZVariable : ShiftedBoundaryPolynomial :=
  MathlibPlus.Open.ResearchFormalization.Claim31331.rootZVariable

abbrev rootVVariable : ShiftedBoundaryPolynomial :=
  MathlibPlus.Open.ResearchFormalization.Claim31331.rootVVariable

/-- The coefficient-ring embedding of a rational scalar into the shifted
boundary polynomial ring. -/
def outerRational (a : ℚ) : ShiftedBoundaryPolynomial :=
  Polynomial.C (Polynomial.C a)

/-- The monic linear factor `z + λv` in the two-variable polynomial ring. -/
def monicLinearBoundaryFactor (lam : ℚˣ) : ShiftedBoundaryPolynomial :=
  rootZVariable + outerRational (lam : ℚ) * rootVVariable

/-- A proper factorization is a factorization by two nonunits. -/
def properShiftedBoundaryFactorization
    (R : RootedFiniteTree) (A B : ShiftedBoundaryPolynomial) : Prop :=
  shiftedBoundaryD R = A * B ∧ ¬ IsUnit A ∧ ¬ IsUnit B

/-- Claim 31327: for order at least three, every proper factorization of the
exact shifted rooted-boundary polynomial contains a rational-unit linear factor
`z + λv`, with the factor transferred back to the polynomial ring. -/
def properFactorizationExposesLinearFactor : Prop :=
  ∀ R : RootedFiniteTree,
    3 ≤ MathlibPlus.Open.ResearchFormalization.Claim31331.vertexCount R →
      ∀ A B : ShiftedBoundaryPolynomial,
        properShiftedBoundaryFactorization R A B →
          ∃ lam : ℚˣ, monicLinearBoundaryFactor lam ∣ A ∨
            ∃ lam : ℚˣ, monicLinearBoundaryFactor lam ∣ B

end

end MathlibPlus.Open.ResearchFormalization.Claim31327
