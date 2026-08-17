import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0867

noncomputable section

/-- The coefficient field `ℚ(x)` and its polynomial ring in `z`. -/
abbrev RationalFunction := RatFunc ℚ
abbrev ZPolynomial := Polynomial RationalFunction

/-- Embedding of a rational scalar into `ℚ(x)[z]`. -/
noncomputable def scalarPolynomial (q : ℚ) : ZPolynomial :=
  Polynomial.C (algebraMap ℚ RationalFunction q)

/-- The bridge factor `λ X - Y` in `ℚ(x)[z]`. -/
noncomputable def bridgeFactor (lambda : ℚ) (X Y : ZPolynomial) : ZPolynomial :=
  scalarPolynomial lambda * X - Y

/-- The normalized common gcd of two translated forms. -/
noncomputable def commonGcd (A B : ZPolynomial) : ZPolynomial :=
  @EuclideanDomain.gcd ZPolynomial inferInstance (Classical.decEq ZPolynomial) A B

/-- Claim 25472: after the translated equation is written with
`A = G X` and `B = G Y`, the coprime bridge factor divides the common gcd. -/
def bridgeFactorDividesCommonGcd25472 : Prop :=
  ∀ (A B D G X Y : ZPolynomial) (lambda : ℚ),
    G = commonGcd A B →
    A = G * X →
    B = G * Y →
    IsCoprime X Y →
    IsCoprime (bridgeFactor lambda X Y) (X * Y) →
    IsUnit (scalarPolynomial (lambda - 1)) →
    D * bridgeFactor lambda X Y =
        scalarPolynomial (lambda - 1) * G * X * Y →
    bridgeFactor lambda X Y ∣ G

end

end MathlibPlus.Open.ResearchFormalization.R0867
