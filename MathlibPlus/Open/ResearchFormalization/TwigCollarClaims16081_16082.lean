import Mathlib
import MathlibPlus.Open.Research.FormalizationBatchUPolynomial

namespace MathlibPlus.Open.ResearchFormalization.TwigCollarClaims16081_16082

open scoped BigOperators

noncomputable section

private abbrev PositiveLeg := {n : ℕ // 0 < n}
private abbrev TwigPartition := Multiset PositiveLeg
private abbrev TwigCollection := Multiset TwigPartition
private abbrev PositiveIndex := {n : ℕ // 0 < n}

private def positiveLegs (A : TwigPartition) : Fin A.card → ℕ :=
  fun i =>
    (A.toList.get ⟨i.1, by simpa using i.2⟩).1

private def pathGraph (m : ℕ) : SimpleGraph (Fin m) :=
  { Adj := fun i j => i.1 + 1 = j.1 ∨ j.1 + 1 = i.1
    symm := ⟨by
      intro i j h
      simpa [or_comm] using h⟩
    loopless := ⟨by
      intro i h
      omega⟩ }

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

private def complementProduct (Λ A : TwigPartition) :
    MvPolynomial ℕ ℚ :=
  ((Λ - A).map (fun b => pathU b.1)).prod

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
  coefficientwisePartialXOne
    ((As.map (twigTerm Λ)).sum)

private def fixedTwigCondition (d r h : ℕ) (Λ : TwigPartition)
    (As : TwigCollection) : Prop :=
  2 ≤ d ∧ 2 ≤ r ∧ r + 1 ≤ h ∧ As.card = d ∧
    (∀ A ∈ As, A.card = r ∧ partitionWeight A = h - 1) ∧
    aggregateTwigs As = Λ

private def mixedTwigCondition (d h : ℕ) (Λ : TwigPartition)
    (As : TwigCollection) : Prop :=
  2 ≤ d ∧ 3 ≤ h ∧ As.card = d ∧
    (∀ A ∈ As, 2 ≤ A.card ∧ partitionWeight A = h - 1) ∧
    aggregateTwigs As = Λ

private def topCoefficient (Λ : TwigPartition) (As : TwigCollection)
    (D : ℕ) : MvPolynomial ℕ ℚ :=
  (twigPsi Λ As).coeff D

private def complementSum (Λ : TwigPartition) (As : TwigCollection) :
    MvPolynomial ℕ ℚ :=
  (As.map (complementProduct Λ)).sum

private def variableCoefficient (k : ℕ) (p : MvPolynomial ℕ ℚ) :
    MvPolynomial ℕ ℚ :=
  ∑ m ∈ p.support,
    if m k = 1 then
      MvPolynomial.monomial (m.erase k) (MvPolynomial.coeff m p)
    else 0

private def pathUsesOnlyEarlier (n : PositiveIndex)
    (p : MvPolynomial ℕ ℚ) : Prop :=
  ∀ m ∈ p.support, ∀ i : ℕ, m i ≠ 0 → 0 < i ∧ i < n.1

private def pathTriangularity : Prop :=
  ∀ n : PositiveIndex, ∃ p : MvPolynomial ℕ ℚ,
    pathU n.1 = MvPolynomial.X n.1 + p ∧
      pathUsesOnlyEarlier n p

private def pathMonomial (parts : Multiset PositiveIndex) :
    MvPolynomial ℕ ℚ :=
  (parts.map (fun n => pathU n.1)).prod

private def pathCoordinateIndependence : Prop :=
  pathTriangularity ∧ LinearIndependent ℚ pathMonomial

/-- Claim 16081: with positive partition parts, the fixed-twig top coefficient
has the exact 1/r inversion formula, and its triangular coordinates recover the
complement and hence the repeated block multiset. -/
def claim16081 : Prop :=
  ∀ (d r h : ℕ) (Λ : TwigPartition) (As : TwigCollection),
    fixedTwigCondition d r h Λ As →
      pathCoordinateIndependence ∧
        let D := (d - 1) * (h - 1)
        let H := topCoefficient Λ As D
        complementSum Λ As =
            (1 / (r : ℚ)) • variableCoefficient (h - 1) H -
              MvPolynomial.X 1 * variableCoefficient h H ∧
          ∀ Bs : TwigCollection,
            fixedTwigCondition d r h Λ Bs →
              topCoefficient Λ As D = topCoefficient Λ Bs D →
                As = Bs

/-- Claim 16082: allowing each positive-part partition to have its own twig
count, the complete derivative collar and already its top cap coefficient
recover the partition multiset with multiplicity. -/
def claim16082 : Prop :=
  ∀ (d h : ℕ) (Λ : TwigPartition)
      (As Bs : TwigCollection),
    mixedTwigCondition d h Λ As →
      mixedTwigCondition d h Λ Bs →
      (twigPsi Λ As = twigPsi Λ Bs → As = Bs) ∧
      (topCoefficient Λ As ((d - 1) * (h - 1)) =
          topCoefficient Λ Bs ((d - 1) * (h - 1)) → As = Bs)

end

end MathlibPlus.Open.ResearchFormalization.TwigCollarClaims16081_16082
