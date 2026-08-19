import MathlibPlus.Open.ResearchFormalization.R0530.Claim26098
import MathlibPlus.Open.ResearchFormalization.R0530Claim26103
import MathlibPlus.Open.ResearchFormalizationBatch019ffedf141b77c7b96e46e312eadae9

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0530Claim26109

noncomputable section

open MathlibPlus.Open.ResearchFormalization.BatchR0532
open MathlibPlus.Open.ResearchFormalizationBatch
open MathlibPlus.Open.ResearchFormalization.R0530.Claim26098
open MathlibPlus.Open.ResearchFormalization.R0530Claim26103

abbrev ProfilePolynomial := MvPolynomial ℕ ℚ
abbrev GeneratingPolynomial := Polynomial ProfilePolynomial

abbrev SingleSpiderVertex (A : Multiset ℕ) := Unit ⊕ LegVertex A

def singleSpiderAdjacency (A : Multiset ℕ)
    (u v : SingleSpiderVertex A) : Prop :=
  match u, v with
  | Sum.inl _, Sum.inl _ => False
  | Sum.inl _, Sum.inr x => x.2.2.val = 0
  | Sum.inr x, Sum.inl _ => x.2.2.val = 0
  | Sum.inr x, Sum.inr y => legAdjacent x y

def singleSpiderGraph26109 (A : Multiset ℕ) :
    SimpleGraph (SingleSpiderVertex A) :=
  SimpleGraph.fromRel (singleSpiderAdjacency A)

def pathGraph26109 (t : ℕ) : SimpleGraph (Fin t) :=
  SimpleGraph.fromRel (fun u v : Fin t => u.val + 1 = v.val)

noncomputable def legGeneratingFactor26109 (ell : ℕ) :
    GeneratingPolynomial :=
  ∑ t ∈ Finset.range (ell + 1),
    (Polynomial.X : GeneratingPolynomial) ^ t *
      Polynomial.C (unsignedConnectedSetPolynomial (pathGraph26109 t))

noncomputable def legGeneratingProduct26109
    (A B : Multiset ℕ) : GeneratingPolynomial :=
  ((A + B).map legGeneratingFactor26109).prod

noncomputable def markedLegGeneratingProduct26109
    (A B : Multiset ℕ) : GeneratingPolynomial :=
  let P := legGeneratingProduct26109 A B
  ∑ n ∈ P.support,
    Polynomial.C (MvPolynomial.pderiv 1 (P.coeff n)) *
      (Polynomial.X : GeneratingPolynomial) ^ n

noncomputable def coefficientOfVariable26109
    (k : ℕ) (P : ProfilePolynomial) : ProfilePolynomial :=
  letI := Classical.decEq (ℕ →₀ ℕ)
  letI := Classical.propDecidable
  ∑ μ ∈ P.support.filter (fun μ => μ k = 1),
    MvPolynomial.monomial (μ - Finsupp.single k 1) (P.coeff μ)

noncomputable def suffixContamination26109
    (A B : Multiset ℕ) (h : ℕ) : ProfilePolynomial :=
  (markedLegGeneratingProduct26109 A B).coeff h

noncomputable def truncationInW26109
    (h : ℕ) (P : GeneratingPolynomial) : GeneratingPolynomial :=
  letI := Classical.decEq ℕ
  letI := Classical.propDecidable
  ∑ n ∈ P.support.filter (fun n => n ≤ h),
    Polynomial.C (P.coeff n) * (Polynomial.X : GeneratingPolynomial) ^ n

noncomputable def leafCoefficient26109 (T : DoubleSpider) : ℚ :=
  (markedSingletonPolynomial (doubleSpiderGraph T)).coeff
    (Finsupp.single (doubleSpiderOrder T - 1) 1)

/-- Claim 26109: the giant coefficient is the smaller terminal-spider
    marked polynomial plus the exact coefficient of the differentiated
    path-factor product; the boundary jet and leaf coefficient recover the
    truncated path product needed to compute that contamination. -/
def exactSmallerTerminalSpiderExtraction_claim26109 : Prop :=
  ∀ T : DoubleSpider,
    admissibleDoubleSpider T →
      T.left.sum < T.right.sum →
        let α := T.left.sum
        let h := α + 1
        let N := doubleSpiderOrder T - h
        coefficientOfVariable26109 N
            (markedSingletonPolynomial (doubleSpiderGraph T)) =
          markedSingletonPolynomial (singleSpiderGraph26109 T.left) +
            suffixContamination26109 T.left T.right h ∧
        coefficientOfVariable26109 N
            (markedSingletonPolynomial (doubleSpiderGraph T)) -
            suffixContamination26109 T.left T.right h =
          markedSingletonPolynomial (singleSpiderGraph26109 T.left) ∧
        ∀ T' : DoubleSpider,
          admissibleDoubleSpider T' →
            T'.left.sum < T'.right.sum →
              degreeAndBoundaryJet T = degreeAndBoundaryJet T' →
                leafCoefficient26109 T = leafCoefficient26109 T' →
                  T.left.sum + 1 = T'.left.sum + 1 ∧
                    truncationInW26109 (T.left.sum + 1)
                        (legGeneratingProduct26109 T.left T.right) =
                      truncationInW26109 (T'.left.sum + 1)
                        (legGeneratingProduct26109 T'.left T'.right)

end

end MathlibPlus.Open.ResearchFormalization.R0530Claim26109
