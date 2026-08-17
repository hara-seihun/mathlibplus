import Mathlib
import MathlibPlus.Open.Research.FormalizationBatchUPolynomial

namespace MathlibPlus.Open.ResearchFormalization.TwigCollarClaims16083

open scoped BigOperators

noncomputable section

private abbrev PositiveLeg := {n : ℕ // 0 < n}
private abbrev TwigPartition := Multiset PositiveLeg
private abbrev TwigCollection := Multiset TwigPartition
private abbrev PositiveIndex := {n : ℕ // 0 < n}

private def positiveLegs (A : TwigPartition) : Fin A.card → ℕ :=
  fun i =>
    (A.toList.get (Fin.cast (Multiset.length_toList A).symm i)).1

private def pathGraph (m : ℕ) : SimpleGraph (Fin m) :=
  { Adj := fun i j => i.1 + 1 = j.1 ∨ j.1 + 1 = i.1
    symm := ⟨fun (i j : Fin m)
      (h : i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) => h.elim Or.inr Or.inl⟩
    loopless := ⟨fun (i : Fin m)
      (h : i.1 + 1 = i.1 ∨ i.1 + 1 = i.1) =>
        h.elim (Nat.add_one_ne_self i.1) (Nat.add_one_ne_self i.1)⟩ }

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
  coefficientwisePartialXOne ((As.map (twigTerm Λ)).sum)

private def mixedTwigCondition (d h : ℕ) (Λ : TwigPartition)
    (As : TwigCollection) : Prop :=
  2 ≤ d ∧ 3 ≤ h ∧ As.card = d ∧
    (∀ A ∈ As, 2 ≤ A.card ∧ partitionWeight A = h - 1) ∧
    aggregateTwigs As = Λ

private def variableCoefficient (k : ℕ) (p : MvPolynomial ℕ ℚ) :
    MvPolynomial ℕ ℚ :=
  ∑ m ∈ p.support,
    if m k = 1 then
      MvPolynomial.monomial (m.erase k) (MvPolynomial.coeff m p)
    else 0

private def eulerOperator (p : MvPolynomial ℕ ℚ) :
    MvPolynomial ℕ ℚ :=
  p + MvPolynomial.X 1 * MvPolynomial.pderiv 1 p

private def eulerInverse (p : MvPolynomial ℕ ℚ) :
    MvPolynomial ℕ ℚ :=
  p.support.sum (fun m =>
    MvPolynomial.monomial m
      (MvPolynomial.coeff m p / ((m 1 + 1 : ℕ) : ℚ)))

private def capProduct (Λ A : TwigPartition) :
    Polynomial (MvPolynomial ℕ ℚ) :=
  ((Λ - A).map (fun b => pathCapPolynomial b.1)).prod

private def weightedComplementPolynomial (Λ : TwigPartition)
    (As : TwigCollection) : Polynomial (MvPolynomial ℕ ℚ) :=
  As.map (fun A => (A.card : ℚ) • capProduct Λ A) |>.sum

private def variableCoefficientPolynomial (k : ℕ)
    (P : Polynomial (MvPolynomial ℕ ℚ)) :
    Polynomial (MvPolynomial ℕ ℚ) :=
  ∑ n ∈ P.support,
    Polynomial.C (variableCoefficient k (P.coeff n)) * Polynomial.X ^ n

private def eulerInversePolynomial
    (P : Polynomial (MvPolynomial ℕ ℚ)) :
    Polynomial (MvPolynomial ℕ ℚ) :=
  ∑ n ∈ P.support,
    Polynomial.C (eulerInverse (P.coeff n)) * Polynomial.X ^ n

private def eulerOperatorPolynomial
    (P : Polynomial (MvPolynomial ℕ ℚ)) :
    Polynomial (MvPolynomial ℕ ℚ) :=
  ∑ n ∈ P.support,
    Polynomial.C (eulerOperator (P.coeff n)) * Polynomial.X ^ n

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

/-- Euler inversion is stated on the reviewed positive-part twig carrier.  The
coefficient rule is explicit, the capped path coordinates are the actual
coordinates used in the collar, and the final implication records recovery of
each complement, hence the block multiset with multiplicity. -/
def claim16083_eulerInversionMixedTwigCounts : Prop :=
  ∀ (d h : ℕ) (Λ : TwigPartition) (As : TwigCollection),
    mixedTwigCondition d h Λ As →
      pathCoordinateIndependence ∧
      (∀ (m : ℕ →₀ ℕ) (c : ℚ),
        eulerInverse (MvPolynomial.monomial m c) =
          MvPolynomial.monomial m
            (c / ((m 1 + 1 : ℕ) : ℚ))) ∧
      (eulerOperatorPolynomial
          (eulerInversePolynomial
            (variableCoefficientPolynomial (h - 1) (twigPsi Λ As))) =
          variableCoefficientPolynomial (h - 1) (twigPsi Λ As) ∧
       eulerInversePolynomial
          (variableCoefficientPolynomial (h - 1) (twigPsi Λ As)) =
          weightedComplementPolynomial Λ As ∧
       ∀ Bs : TwigCollection,
         mixedTwigCondition d h Λ Bs →
           weightedComplementPolynomial Λ As =
             weightedComplementPolynomial Λ Bs →
             As = Bs)

end

end MathlibPlus.Open.ResearchFormalization.TwigCollarClaims16083
