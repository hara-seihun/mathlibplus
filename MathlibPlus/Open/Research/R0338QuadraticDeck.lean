import Mathlib
import MathlibPlus.GraphTheory.Claim28295
import MathlibPlus.Open.Combinatorics.TreeDeck

open scoped BigOperators
open ProjectsResearch.TreeDeck
noncomputable section

namespace MathlibPlus.Open.Research.R0338

abbrev LabelledTree (n : ℕ) := ProjectsResearch.TreeDeck.LabelledTree n
abbrev UnlabelledTree (n : ℕ) := ProjectsResearch.TreeDeck.UnlabelledTree n

def realizedTrees (n : ℕ) : Finset (UnlabelledTree n) :=
  letI : DecidablePred (fun G : SimpleGraph (Fin n) => G.IsTree) :=
    fun G => Classical.propDecidable (G.IsTree)
  letI : DecidableEq (UnlabelledTree n) := Classical.decEq _
  (Finset.univ.filter (fun G : SimpleGraph (Fin n) => G.IsTree)).attach.image
    (fun G => Quotient.mk (ProjectsResearch.TreeDeck.treeSetoid n)
      (⟨G.1, (Finset.mem_filter.mp G.2).2⟩ : LabelledTree n))

def RealizedTreeIndex (n : ℕ) := Fin (realizedTrees n).card

def realizedTreeAt (n : ℕ) (i : RealizedTreeIndex n) : UnlabelledTree n :=
  ((Finset.equivFin (realizedTrees n)).symm i).1

def treeRepresentative {n : ℕ} (T : UnlabelledTree n) : SimpleGraph (Fin n) :=
  (Quotient.out T).1

def multisetExponent (part : Multiset ℕ) : ℕ →₀ ℕ :=
  (part.map (fun k => Finsupp.single k 1)).sum

def partitionMonomial (part : Multiset ℕ) : MvPolynomial ℕ ℚ :=
  (part.map (fun k => MvPolynomial.X k)).prod

def graphEdgeFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finset (Sym2 V) :=
  letI : DecidablePred (fun e : Sym2 V => e ∈ G.edgeSet) :=
    fun e => Classical.propDecidable (e ∈ G.edgeSet)
  (Finset.univ : Finset (Sym2 V)).filter (fun e => e ∈ G.edgeSet)

def cutPolynomial {n : ℕ} (G : SimpleGraph (Fin n)) : MvPolynomial ℕ ℚ :=
  ∑ E ∈ (graphEdgeFinset G).powerset,
    (-1 : ℚ) ^ E.card •
      partitionMonomial
        (MathlibPlus.GraphTheory.Claim28295.componentSizes
          (SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n)))) )

def deckSum {n : ℕ} (G : SimpleGraph (Fin n)) : MvPolynomial ℕ ℚ :=
  MvPolynomial.pderiv 1 (cutPolynomial G)

def deckCoefficient {n : ℕ} (G : SimpleGraph (Fin n))
    (part : Multiset ℕ) : ℚ :=
  MvPolynomial.coeff (multisetExponent part) (deckSum G)

def treeDeckCoefficient {n : ℕ} (T : UnlabelledTree n)
    (part : Multiset ℕ) : ℚ :=
  deckCoefficient (treeRepresentative T) part

def coefficientFunction {n : ℕ} (μ : Nat.Partition (n - 1)) :
    RealizedTreeIndex n → ℚ :=
  fun i => treeDeckCoefficient (realizedTreeAt n i) μ.parts

def featureIndex (n : ℕ) :=
  Unit ⊕ Nat.Partition (n - 1) ⊕
    (Nat.Partition (n - 1) × Nat.Partition (n - 1))

def quadraticFeature {n : ℕ} (i : featureIndex n) :
    RealizedTreeIndex n → ℚ :=
  match i with
  | Sum.inl _ => fun _ => 1
  | Sum.inr (Sum.inl μ) => coefficientFunction μ
  | Sum.inr (Sum.inr (μ, ν)) =>
      fun T => coefficientFunction μ T * coefficientFunction ν T

def quadraticFeatureSpace (n : ℕ) :
    Submodule ℚ (RealizedTreeIndex n → ℚ) :=
  Submodule.span ℚ (Set.range (quadraticFeature (n := n)))

def claim20089 : Prop :=
  (∀ n : ℕ, 4 ≤ n → n ≤ 10 →
    quadraticFeatureSpace n = ⊤) ∧
    quadraticFeatureSpace 11 ≠ ⊤ ∧
    Module.finrank ℚ (quadraticFeatureSpace 11) + 1 =
      (realizedTrees 11).card ∧
    (realizedTrees 11).card = 235 ∧
    Module.finrank ℚ (quadraticFeatureSpace 11) = 234

end MathlibPlus.Open.Research.R0338
