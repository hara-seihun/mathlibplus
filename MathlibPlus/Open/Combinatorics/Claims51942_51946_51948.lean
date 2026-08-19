import MathlibPlus.Open.Combinatorics.Claims51949_51951

namespace MathlibPlus.Open.Combinatorics.StanleyAugmentationClaims51942_51948

noncomputable section

open MathlibPlus.Open.Combinatorics.StanleyAugmentation

attribute [local instance] Classical.propDecidable Classical.decEq

abbrev TreePolynomial :=
  MathlibPlus.Open.Combinatorics.StanleyAugmentation.TreePolynomial

/-- Claim 51942: nonisomorphic equal-order trees with equal ordinary U have
 disjoint sets of one-leaf augmentation values, with vertex occurrences kept. -/
def claim51942 : Prop :=
  ∀ {V W : Type*} [Fintype V] [Fintype W]
    (T : SimpleGraph V) (T' : SimpleGraph W) (n : ℕ),
    T.IsTree → T'.IsTree →
      Fintype.card V = n → Fintype.card W = n →
        ¬ Nonempty (T ≃g T') →
          treeU T = treeU T' →
            Disjoint (Set.range (augmentationValue T))
              (Set.range (augmentationValue T'))

/-- The two augmentation-root polynomials after passage to the fraction
field of the exact TreePolynomial coefficient ring. -/
def mappedAugmentationLambda
    {V : Type*} [Fintype V] (T : SimpleGraph V) :
    Polynomial (FractionRing TreePolynomial) :=
  Polynomial.map
    (algebraMap TreePolynomial (FractionRing TreePolynomial))
    (augmentationLambda T)

/-- Claim 51946: the exact occurrence-multiplicity augmentation polynomials
have no common linear factor and are coprime over the coefficient fraction
field. -/
def claim51946 : Prop :=
  ∀ {V W : Type*} [Fintype V] [Fintype W]
    (T : SimpleGraph V) (T' : SimpleGraph W) (n : ℕ),
    T.IsTree → T'.IsTree →
      Fintype.card V = n → Fintype.card W = n →
        ¬ Nonempty (T ≃g T') →
          treeU T = treeU T' →
            let P := mappedAugmentationLambda T
            let Q := mappedAugmentationLambda T'
            (∀ L : Polynomial (FractionRing TreePolynomial),
              L.degree = 1 → ¬ (L ∣ P ∧ L ∣ Q)) ∧
              IsCoprime P Q

/-- The first differential `D₁=Σ_k k x_(k+1)∂_(x_k)` on the exact
multivariate TreePolynomial carrier. -/
noncomputable def dOne51948 (P : TreePolynomial) : TreePolynomial :=
  ∑ k ∈ P.vars,
    MvPolynomial.C (k : ℤ) * MvPolynomial.X (k + 1) *
      MvPolynomial.pderiv k P

/-- Claim 51948: the first elementary augmentation coefficient is the sum of
vertex-occurrence values and equals `(n*x₁+D₁)U`; equal-U hosts therefore have
equal first coefficients. -/
def claim51948 : Prop :=
  ∀ {V : Type*} [Fintype V]
    (T : SimpleGraph V) (n : ℕ),
    T.IsTree → Fintype.card V = n →
      elementaryCoefficient T 1 =
          ∑ v : V, augmentationValue T v ∧
        elementaryCoefficient T 1 =
          MvPolynomial.C (n : ℤ) * MvPolynomial.X 1 * treeU T +
            dOne51948 (treeU T) ∧
        ∀ {W : Type*} [Fintype W]
          (T' : SimpleGraph W),
          T'.IsTree → Fintype.card W = n → treeU T = treeU T' →
            elementaryCoefficient T 1 = elementaryCoefficient T' 1

end

end MathlibPlus.Open.Combinatorics.StanleyAugmentationClaims51942_51948
