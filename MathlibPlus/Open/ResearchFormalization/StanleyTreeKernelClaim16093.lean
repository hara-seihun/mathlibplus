import Mathlib
import MathlibPlus.Open.TreeSpectral
import MathlibPlus.Open.Research.FormalizationBatchUPolynomial

namespace MathlibPlus.Open.ResearchFormalization.StanleyTreeKernelClaim16093

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

private abbrev PositiveOrder := {n : ℕ // 0 < n}
private abbrev TreeType := Σ n : PositiveOrder,
  MathlibPlus.Open.TreeSpectral.TreeClass n.1

private def treeOrder (τ : TreeType) : ℕ := τ.1.1

private def treeRepresentative (τ : TreeType) : SimpleGraph (Fin (treeOrder τ)) :=
  (Quotient.out τ.2).1

private def inducedReachability {n : ℕ} (G : SimpleGraph (Fin n))
    (B : Finset (Fin n)) (u v : Fin n) : Prop :=
  u ∈ B ∧ v ∈ B ∧ G.Adj u v

private def componentSet {n : ℕ} (G : SimpleGraph (Fin n))
    (B : Finset (Fin n)) (v : Fin n) : Finset (Fin n) :=
  B.filter (fun w =>
    Relation.ReflTransGen (inducedReachability G B) v w)

private def componentBlocks {n : ℕ} (G : SimpleGraph (Fin n))
    (B : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Finset (Fin n))).filter (fun C =>
    C.Nonempty ∧ ∃ v, v ∈ B ∧ componentSet G B v = C)

private def componentGraph {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Finset (Fin n)) : SimpleGraph (Fin C.card) :=
  let hcard : Fintype.card {x : Fin n // x ∈ C} = C.card := Fintype.card_coe C
  let e : {x : Fin n // x ∈ C} ≃ Fin C.card :=
    Fintype.equivFinOfCardEq hcard
  SimpleGraph.comap e.symm (G.induce (C : Set (Fin n)))

private def componentTreeFactor {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Finset (Fin n)) : MvPolynomial TreeType ℤ :=
  if hC : 0 < C.card then
    let H := componentGraph G C
    if h : ∃ q : MathlibPlus.Open.TreeSpectral.TreeClass C.card,
        Nonempty (H ≃g (Quotient.out q).1) then
      MvPolynomial.X ⟨⟨C.card, hC⟩, Classical.choose h⟩
    else 1
  else 1

private def isSetPartition {n : ℕ}
    (π : Finset (Finset (Fin n))) : Prop :=
  (∀ B ∈ π, B.Nonempty) ∧
    π.biUnion id = Finset.univ ∧
      (∀ B ∈ π, ∀ C ∈ π, B ≠ C → Disjoint B C)

private def partitionFamily (n : ℕ) :
    Finset (Finset (Finset (Fin n))) :=
  Finset.univ.filter isSetPartition

private def partitionMobius {n : ℕ}
    (π : Finset (Finset (Fin n))) : ℤ :=
  (-1 : ℤ) ^ (π.card - 1) * (π.card - 1).factorial

private def forestRestrictionMonomial (τ : TreeType)
    (π : Finset (Finset (Fin (treeOrder τ)))) :
    MvPolynomial TreeType ℤ :=
  ∏ B ∈ π, ∏ C ∈ componentBlocks (treeRepresentative τ) B,
    componentTreeFactor (treeRepresentative τ) C

private def treeCumulant (τ : TreeType) : MvPolynomial TreeType ℤ :=
  ∑ π ∈ partitionFamily (treeOrder τ),
    partitionMobius π • forestRestrictionMonomial τ π

private def treeGenerator (τ : TreeType) : MvPolynomial TreeType ℤ :=
  MvPolynomial.X τ

private def powerSumMonomial {n : ℕ}
    (E : Finset (Sym2 (Fin n))) : MvPolynomial ℕ ℤ :=
  ∏ C ∈ MathlibPlus.Open.ResearchFormalizationBatch.uComponents E,
    MvPolynomial.X C.card

private def treeChromaticGenerator (τ : TreeType) :
    MvPolynomial ℕ ℤ :=
  let G := treeRepresentative τ
  (Finset.powerset
      (MathlibPlus.Open.ResearchFormalizationBatch.uEdgeUniverse G)).sum
    (fun E => ((-1 : ℤ) ^ E.card) • powerSumMonomial E)

private def treeChromaticMap :
    MvPolynomial TreeType ℤ →+* MvPolynomial ℕ ℤ :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C : ℤ →+* MvPolynomial ℕ ℤ)
    treeChromaticGenerator

private def qPowerSum (τ : TreeType) : MvPolynomial ℕ ℤ :=
  ((-1 : ℤ) ^ (treeOrder τ - 1)) •
    MvPolynomial.X (treeOrder τ)

private def chromaticCumulantImage : Prop :=
  ∀ τ : TreeType,
    treeChromaticMap (treeCumulant τ) = qPowerSum τ

private def referenceTree (ρ : ∀ n : PositiveOrder,
    MathlibPlus.Open.TreeSpectral.TreeClass n.1)
    (n : PositiveOrder) : TreeType :=
  ⟨n, ρ n⟩

private def referenceCumulantDifference
    (ρ : ∀ n : PositiveOrder,
      MathlibPlus.Open.TreeSpectral.TreeClass n.1)
    (τ : TreeType) : MvPolynomial TreeType ℤ :=
  treeCumulant τ -
    treeCumulant (referenceTree ρ ⟨treeOrder τ, τ.1.2⟩)

private def treeKernelIdeal
    (ρ : ∀ n : PositiveOrder,
      MathlibPlus.Open.TreeSpectral.TreeClass n.1) :
    Ideal (MvPolynomial TreeType ℤ) :=
  Ideal.span (Set.range (referenceCumulantDifference ρ))

private def powerSumOrder (n : PositiveOrder) : MvPolynomial ℕ ℤ :=
  ((-1 : ℤ) ^ (n.1 - 1)) • MvPolynomial.X n.1

private def powerSumMap :
    MvPolynomial PositiveOrder ℤ →+* MvPolynomial ℕ ℤ :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C : ℤ →+* MvPolynomial ℕ ℤ)
    powerSumOrder

private def quotientNormalForm
    (ρ : ∀ n : PositiveOrder,
      MathlibPlus.Open.TreeSpectral.TreeClass n.1) : Prop :=
  ∃ e : (MvPolynomial TreeType ℤ ⧸ treeKernelIdeal ρ) ≃+*
      MvPolynomial PositiveOrder ℤ,
    (∀ n : PositiveOrder,
      e (Ideal.Quotient.mk (treeKernelIdeal ρ)
        (treeCumulant (referenceTree ρ n))) = MvPolynomial.X n) ∧
      (∀ τ : TreeType,
        e (Ideal.Quotient.mk (treeKernelIdeal ρ) (treeCumulant τ)) =
          MvPolynomial.X ⟨treeOrder τ, τ.1.2⟩) ∧
      (∀ p : MvPolynomial TreeType ℤ,
        treeChromaticMap p =
          powerSumMap (e (Ideal.Quotient.mk (treeKernelIdeal ρ) p)))

private def inducedPowerSumValues : Prop :=
  ∀ n : PositiveOrder,
    powerSumMap (MvPolynomial.X n) = powerSumOrder n

/-- Claim 16093: the exact reference-tree cumulant ideal is the chromatic
    kernel; its quotient is the polynomial ring on one variable in each
    positive order, and its induced signed power-sum map is injective. -/
def claim16093 : Prop :=
  chromaticCumulantImage ∧
    inducedPowerSumValues ∧
      Function.Injective powerSumMap ∧
        ∀ ρ : ∀ n : PositiveOrder,
          MathlibPlus.Open.TreeSpectral.TreeClass n.1,
          RingHom.ker treeChromaticMap = treeKernelIdeal ρ ∧
            quotientNormalForm ρ

end

end MathlibPlus.Open.ResearchFormalization.StanleyTreeKernelClaim16093
