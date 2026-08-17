import Mathlib
import MathlibPlus.Open.Research.FormalizationBatchUPolynomial

namespace MathlibPlus.Open.ResearchFormalization.Claim16080FixedTwig

open scoped BigOperators

noncomputable section

private abbrev PositiveLeg := {n : ℕ // 0 < n}
private abbrev TwigPartition := Multiset PositiveLeg
private abbrev TwigCollection := Multiset TwigPartition

private def positiveLegs (A : TwigPartition) : Fin A.card → ℕ :=
  fun i =>
    (A.toList.get (Fin.cast (Multiset.length_toList A).symm i)).1

private def pathGraph (m : ℕ) : SimpleGraph (Fin m) :=
  SimpleGraph.fromRel (fun i j => i.1 + 1 = j.1 ∨ j.1 + 1 = i.1)

private def castMvQRingHom : MvPolynomial ℕ ℤ →+* MvPolynomial ℕ ℚ :=
  MvPolynomial.map (Int.castRingHom ℚ)

private def castMvQ (p : MvPolynomial ℕ ℤ) : MvPolynomial ℕ ℚ :=
  castMvQRingHom p

private def pathU (m : ℕ) : MvPolynomial ℕ ℚ :=
  castMvQ (MathlibPlus.Open.ResearchFormalizationBatch.forestUPolynomial
    (pathGraph m))

private def spiderU (A : TwigPartition) : MvPolynomial ℕ ℚ :=
  castMvQ (MathlibPlus.Open.ResearchFormalizationBatch.forestUPolynomial
    (MathlibPlus.Open.ResearchFormalizationBatch.spiderGraph (positiveLegs A)))

private def pathCapPolynomial (a : ℕ) :
    Polynomial (MvPolynomial ℕ ℚ) :=
  ∑ q ∈ Finset.range (a + 1),
    Polynomial.X ^ q * Polynomial.C (pathU q)

private def partitionWeight (A : TwigPartition) : ℕ :=
  (A.map (fun p => p.1)).sum

private def aggregateTwigs (As : TwigCollection) : TwigPartition :=
  As.sum

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

private def fixedTwigCondition (d r h : ℕ) (Λ : TwigPartition)
    (As : TwigCollection) : Prop :=
  2 ≤ d ∧ 2 ≤ r ∧ r + 1 ≤ h ∧ As.card = d ∧
    (∀ A ∈ As, A.card = r ∧ partitionWeight A = h - 1) ∧
    aggregateTwigs As = Λ

private def topCoefficient (Λ : TwigPartition) (As : TwigCollection)
    (D : ℕ) : MvPolynomial ℕ ℚ :=
  (twigPsi Λ As).coeff D

/-- Claim 16080: on fixed positive-leg partitions with fixed aggregate, the
complete derivative collar is injective, and the single stated top coefficient
already determines the grouping with multiplicity. -/
def claim16080 : Prop :=
  ∀ (d r h : ℕ) (Λ : TwigPartition)
    (As Bs : TwigCollection),
    fixedTwigCondition d r h Λ As →
    fixedTwigCondition d r h Λ Bs →
    (twigPsi Λ As = twigPsi Λ Bs → As = Bs) ∧
      (topCoefficient Λ As ((d - 1) * (h - 1)) =
        topCoefficient Λ Bs ((d - 1) * (h - 1)) → As = Bs)

end

end MathlibPlus.Open.ResearchFormalization.Claim16080FixedTwig
