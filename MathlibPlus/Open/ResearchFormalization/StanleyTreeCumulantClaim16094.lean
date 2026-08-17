import Mathlib
import MathlibPlus.Open.TreeSpectral
import MathlibPlus.Open.Research.FormalizationBatchUPolynomial

namespace MathlibPlus.Open.ResearchFormalization.StanleyTreeCumulantClaim16094

open scoped BigOperators

noncomputable section

private abbrev PositiveOrder := {n : ℕ // 0 < n}
private abbrev TreeType :=
  Σ n : PositiveOrder, MathlibPlus.Open.TreeSpectral.TreeClass n.1

private def treeOrder (τ : TreeType) : ℕ := τ.1.1

private def treeRepresentative (τ : TreeType) :
    SimpleGraph (Fin (treeOrder τ)) :=
  (Quotient.out τ.2).1

private def inducedReachability {n : ℕ} (G : SimpleGraph (Fin n))
    (B : Finset (Fin n)) (u v : Fin n) : Prop :=
  u ∈ B ∧ v ∈ B ∧ G.Adj u v

private def componentSet {n : ℕ} (G : SimpleGraph (Fin n))
    (B : Finset (Fin n)) (v : Fin n) : Finset (Fin n) := by
  classical
  exact B.filter (fun w =>
    Relation.ReflTransGen (inducedReachability G B) v w)

private def componentBlocks {n : ℕ} (G : SimpleGraph (Fin n))
    (B : Finset (Fin n)) : Finset (Finset (Fin n)) := by
  classical
  exact (Finset.univ : Finset (Finset (Fin n))).filter (fun C =>
    C.Nonempty ∧ ∃ v, v ∈ B ∧ componentSet G B v = C)

private def componentGraph {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Finset (Fin n)) : SimpleGraph (Fin C.card) := by
  classical
  have hcard : Fintype.card {x : Fin n // x ∈ C} = C.card :=
    Fintype.card_coe C
  let e : {x : Fin n // x ∈ C} ≃ Fin C.card :=
    Fintype.equivFinOfCardEq hcard
  exact SimpleGraph.comap e.symm (G.induce (C : Set (Fin n)))

private def componentTreeFactor {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Finset (Fin n)) : MvPolynomial TreeType ℤ := by
  classical
  by_cases hC : 0 < C.card
  · let H := componentGraph G C
    by_cases h : ∃ q : MathlibPlus.Open.TreeSpectral.TreeClass C.card,
        Nonempty (H ≃g (Quotient.out q).1)
    · exact MvPolynomial.X
        ⟨⟨C.card, hC⟩, Classical.choose h⟩
    · exact 1
  · exact 1

private def isSetPartition {n : ℕ}
    (π : Finset (Finset (Fin n))) : Prop := by
  classical
  exact
    (∀ B ∈ π, B.Nonempty) ∧
      π.biUnion id = Finset.univ ∧
      (∀ B ∈ π, ∀ C ∈ π, B ≠ C → Disjoint B C)

private def partitionFamily (n : ℕ) :
    Finset (Finset (Finset (Fin n))) := by
  classical
  exact Finset.univ.filter isSetPartition

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

private def lowerTreePolynomial (τ : TreeType)
    (p : MvPolynomial TreeType ℤ) : Prop :=
  ∀ m ∈ p.support, ∀ σ ∈ m.support, treeOrder σ < treeOrder τ

private def cumulantSubstitution :
    MvPolynomial TreeType ℤ →+* MvPolynomial TreeType ℤ :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C : ℤ →+* MvPolynomial TreeType ℤ)
    treeCumulant

private def treeCumulantsUnitriangular : Prop :=
  (∀ τ : TreeType, ∃ p : MvPolynomial TreeType ℤ,
    treeCumulant τ = treeGenerator τ + p ∧
      lowerTreePolynomial τ p) ∧
  (∀ τ : TreeType, ∃ p : MvPolynomial TreeType ℤ,
    cumulantSubstitution p = treeGenerator τ)

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

private abbrev ReferenceFamily :=
  ∀ n : PositiveOrder,
    MathlibPlus.Open.TreeSpectral.TreeClass n.1

private def referenceTree (ρ : ReferenceFamily) (n : PositiveOrder) :
    TreeType :=
  ⟨n, ρ n⟩

private def treeKernelIdeal (ρ : ReferenceFamily) :
    Ideal (MvPolynomial TreeType ℤ) :=
  Ideal.span (Set.range (fun τ : TreeType =>
    treeCumulant τ - treeCumulant
      (referenceTree ρ ⟨treeOrder τ, τ.1.2⟩)))

private def treeChromaticOnGenerators :
    TreeType → MvPolynomial ℕ ℤ :=
  fun τ => treeChromaticMap (treeGenerator τ)

/-- Claim 16094: the Stanley tree-injectivity question is exactly the
same-order cumulant identification and its ideal-membership normal form; no
solution of the remaining binomial-intersection question is asserted. -/
def claim16094 : Prop :=
  treeCumulantsUnitriangular ∧
    chromaticCumulantImage ∧
    ∀ ρ : ReferenceFamily,
      RingHom.ker treeChromaticMap = treeKernelIdeal ρ ∧
        (Function.Injective treeChromaticOnGenerators ↔
          ∀ τ σ : TreeType, τ ≠ σ →
            treeGenerator τ - treeGenerator σ ∉ treeKernelIdeal ρ)

end

end MathlibPlus.Open.ResearchFormalization.StanleyTreeCumulantClaim16094
