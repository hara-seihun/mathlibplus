import MathlibPlus.Open.ResearchFormalization.ScalarRootedFactors

namespace MathlibPlus.Open.ResearchFormalization.BatchR0741Claim24428

noncomputable section

open Polynomial

private abbrev Coeff :=
  MathlibPlus.Open.ResearchFormalization.CoefficientRing
private abbrev Root :=
  MathlibPlus.Open.ResearchFormalization.RootRing

private def ratCoeff (q : ℚ) : Coeff := algebraMap ℚ Coeff q

/-- The common largest component variable is the polynomial variable of the
rooted-factor ring; all four offsets live in its coefficient ring. -/
private def sourceA0 (a : Coeff) : Root :=
  Polynomial.X + Polynomial.C a

private def sourceA1 (a U : Coeff) : Root :=
  sourceA0 a + Polynomial.C U

private def sourceC0 (c : Coeff) : Root :=
  Polynomial.X + Polynomial.C c

private def sourceC1 (c V : Coeff) : Root :=
  sourceC0 c + Polynomial.C V

private def sourceSquareFactors (a c U V : Coeff) : Fin 4 → Root :=
  ![sourceA0 a, sourceA1 a U, sourceC0 c, sourceC1 c V]

private def rationalAffineLineFactors (a U s r : Coeff) : Fin 4 → Root :=
  ![sourceA0 a,
    sourceA0 a + Polynomial.C U,
    sourceA0 a + Polynomial.C (s * U),
    sourceA0 a + Polynomial.C ((s + r) * U)]

/-- The normalized product-square relation in the rooted-factor ring. -/
private def productSquareRelation (a c U V : Coeff)
    (β γ δ : ℚ) : Prop :=
  Polynomial.C (ratCoeff β * U) * sourceC0 c +
      Polynomial.C (ratCoeff γ * V) * sourceA0 a +
        Polynomial.C (ratCoeff δ * U * V) = 0

/-- Claim 24428: in the genuine normalized rooted-factor carrier, a nontrivial
rational proportional relation forces the four source factors onto the stated
rational affine line. -/
def claim24428_proportionalRelationForcesSourceCollinearity : Prop :=
  ∀ (a c U V : Coeff) (β γ δ r : ℚ),
    U ≠ 0 →
    V ≠ 0 →
    r ≠ 0 →
    V = ratCoeff r * U →
    ¬(β = 0 ∧ γ = 0 ∧ δ = 0) →
    productSquareRelation a c U V β γ δ →
      γ = -β / r ∧
      U * (ratCoeff β * (c - a) + ratCoeff δ * ratCoeff r * U) = 0 ∧
      ∃ s : ℚ,
        c - a = ratCoeff s * U ∧
        sourceSquareFactors a c U V =
          rationalAffineLineFactors a U (ratCoeff s) (ratCoeff r)

end
end MathlibPlus.Open.ResearchFormalization.BatchR0741Claim24428
