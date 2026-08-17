import Mathlib
import MathlibPlus.Open.Research.FormalizationBatchUPolynomial

namespace MathlibPlus.Open.ResearchFormalization.TwigCollarStressClaim16084

open scoped BigOperators

noncomputable section

private abbrev PositiveLeg := {n : ℕ // 0 < n}
private abbrev TwigPartition := Multiset PositiveLeg
private abbrev TwigCollection := Multiset TwigPartition

private def pathGraph (m : ℕ) : SimpleGraph (Fin m) :=
  SimpleGraph.fromRel (fun i j => i.1 + 1 = j.1 ∨ j.1 + 1 = i.1)

private def castMvQRingHom : MvPolynomial ℕ ℤ →+* MvPolynomial ℕ ℚ :=
  MvPolynomial.map (Int.castRingHom ℚ)

private def castMvQ (p : MvPolynomial ℕ ℤ) : MvPolynomial ℕ ℚ :=
  castMvQRingHom p

private def pathU (m : ℕ) : MvPolynomial ℕ ℚ :=
  castMvQ (MathlibPlus.Open.ResearchFormalizationBatch.forestUPolynomial
    (pathGraph m))

private def positiveLegs (A : TwigPartition) : Fin A.card → ℕ :=
  fun i =>
    (A.toList.get
      ⟨i.1, (Multiset.length_toList A).symm ▸ i.2⟩).1

private def spiderU (A : TwigPartition) : MvPolynomial ℕ ℚ :=
  castMvQ (MathlibPlus.Open.ResearchFormalizationBatch.forestUPolynomial
    (MathlibPlus.Open.ResearchFormalizationBatch.spiderGraph (positiveLegs A)))

private def pathCapPolynomial (a : ℕ) :
    Polynomial (MvPolynomial ℕ ℚ) :=
  ∑ q ∈ Finset.range (a + 1),
    Polynomial.X ^ q * Polynomial.C (pathU q)

private def twigTerm (Λ A : TwigPartition) :
    Polynomial (MvPolynomial ℕ ℚ) :=
  Polynomial.C (spiderU A) *
    ((Λ - A).map (fun b => pathCapPolynomial b.1)).prod

private def coefficientwisePartialXOne
    (P : Polynomial (MvPolynomial ℕ ℚ)) :
    Polynomial (MvPolynomial ℕ ℚ) :=
  ∑ n ∈ P.support,
    Polynomial.C (MvPolynomial.pderiv 1 (P.coeff n)) * Polynomial.X ^ n

private def twigPsi (Λ : TwigPartition) (As : TwigCollection) :
    Polynomial (MvPolynomial ℕ ℚ) :=
  coefficientwisePartialXOne ((As.map (twigTerm Λ)).sum)

private def aggregateTwigs (As : TwigCollection) : TwigPartition :=
  As.sum

private def weightedComplementPolynomial (Λ : TwigPartition)
    (As : TwigCollection) : Polynomial (MvPolynomial ℕ ℚ) :=
  (As.map (fun A =>
    (A.card : ℚ) • ((Λ - A).map (fun b => pathCapPolynomial b.1)).prod)).sum

private def positiveLeg (n : ℕ) : PositiveLeg :=
  ⟨n + 1, Nat.zero_lt_succ n⟩

private def stressA : TwigCollection :=
  Multiset.cons
    ({positiveLeg 0, positiveLeg 3, positiveLeg 3} : TwigPartition)
    (Multiset.cons
      ({positiveLeg 1, positiveLeg 1, positiveLeg 4} : TwigPartition)
      (Multiset.cons
        ({positiveLeg 2, positiveLeg 2, positiveLeg 2} : TwigPartition)
        0))

private def stressB : TwigCollection :=
  Multiset.cons
    ({positiveLeg 0, positiveLeg 2, positiveLeg 4} : TwigPartition)
    (Multiset.cons
      ({positiveLeg 1, positiveLeg 2, positiveLeg 3} : TwigPartition)
      (Multiset.cons
        ({positiveLeg 1, positiveLeg 2, positiveLeg 3} : TwigPartition)
        0))

private def stressAggregateA : TwigPartition := aggregateTwigs stressA
private def stressAggregateB : TwigPartition := aggregateTwigs stressB

private def stressMonomial : ℕ →₀ ℕ :=
  Finsupp.single 1 1 + Finsupp.single 4 1 + Finsupp.single 6 1

private def monomialCoefficient (p : MvPolynomial ℕ ℚ) (m : ℕ →₀ ℕ) : ℚ :=
  p.coeff m

/-- Claim 16084: the displayed order-ten grouping collision survives the
weighted complement projection through `t⁵`, but the full derivative collar
separates the groupings at `t²`. -/
def claim16084 : Prop :=
  stressAggregateA = stressAggregateB ∧
    (∀ q : ℕ, q ≤ 5 →
      (weightedComplementPolynomial stressAggregateA stressA).coeff q =
        (weightedComplementPolynomial stressAggregateB stressB).coeff q) ∧
    (weightedComplementPolynomial stressAggregateA stressA).coeff 6 ≠
      (weightedComplementPolynomial stressAggregateB stressB).coeff 6 ∧
    (twigPsi stressAggregateA stressA).coeff 2 ≠
      (twigPsi stressAggregateB stressB).coeff 2 ∧
    monomialCoefficient
        ((twigPsi stressAggregateA stressA).coeff 2)
        stressMonomial -
      monomialCoefficient
        ((twigPsi stressAggregateB stressB).coeff 2)
        stressMonomial = 2

end

end MathlibPlus.Open.ResearchFormalization.TwigCollarStressClaim16084
