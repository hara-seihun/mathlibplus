import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.GraphTheory.R3537

noncomputable section

private def graphEdges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finset (Sym2 V) :=
  G.edgeSet.toFinite.toFinset

private def monochromaticEdges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (c : V → Bool) : Finset (Sym2 V) :=
  graphEdges G |>.filter (fun e => (e.toFinset.image c).card = 1)

private def crossingEdges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (c : V → Bool) : Finset (Sym2 V) :=
  graphEdges G |>.filter (fun e => (e.toFinset.image c).card = 2)

private def cutBoundaryEdges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : Finset (Sym2 V) :=
  graphEdges G |>.filter (fun e =>
    (e.toFinset.image (fun v => v ∈ S)).card = 2)

private def switchColor {V : Type*} [DecidableEq V]
    (c : V → Bool) (S : Finset V) : V → Bool :=
  fun v => if v ∈ S then !c v else c v

private def maximumCut {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (c : V → Bool) : Prop :=
  ∀ S : Finset V,
    (crossingEdges G (switchColor c S)).card ≤ (crossingEdges G c).card

private def crossingGraph {V : Type*} (G : SimpleGraph V) (c : V → Bool) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v => G.Adj u v ∧ c u ≠ c v)

private def componentPartition {V : Type*} [Fintype V] [DecidableEq V]
    (B : SimpleGraph V) (parts : Finset (Finset V)) : Prop :=
  (∀ P ∈ parts, P.Nonempty) ∧
    (∀ P ∈ parts, ∀ Q ∈ parts, P ≠ Q → Disjoint P Q) ∧
    (∀ v : V, ∃ P ∈ parts, v ∈ P) ∧
    (∀ u v : V,
      (∃ P ∈ parts, u ∈ P ∧ v ∈ P) ↔ B.Reachable u v)

private noncomputable def bipartizationNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  sInf {n : ℕ | ∃ c : V → Bool, (monochromaticEdges G c).card = n}

private def triangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ ⦃u v w : V⦄,
    u ≠ v → v ≠ w → w ≠ u →
    G.Adj u v → G.Adj v w → G.Adj w u → False

private def inducedGraph {V : Type*} (G : SimpleGraph V) (P : Finset V) :
    SimpleGraph {v // v ∈ (P : Set V)} :=
  G.induce (P : Set V)

private def componentSize {V : Type*} [Fintype V] (P : Finset V) : ℕ :=
  Fintype.card {v // v ∈ (P : Set V)}

/-- Claim 47857: switching a maximum cut cannot increase its size, and the
lost monochromatic boundary edges are no more numerous than the lost crossing
boundary edges.  A Boolean coloring is the displayed partition `A ⊔ C`. -/
def switchingInequalityMaximumCutClaim47857 : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (c : V → Bool),
    maximumCut G c →
      ∀ S : Finset V,
        ((monochromaticEdges G c) ∩ (cutBoundaryEdges G S)).card ≤
          ((crossingEdges G c) ∩ (cutBoundaryEdges G S)).card

/-- Claim 47859: under a maximum cut, the connected components of the
crossing-edge graph are exactly the connected components of the whole graph. -/
def crossingComponentsAreGraphComponentsClaim47859 : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (c : V → Bool),
    maximumCut G c →
      ∀ u v : V,
        (crossingGraph G c).Reachable u v ↔ G.Reachable u v

/-- Claim 47861: once the crossing components are represented by an explicit
partition, the restricted cut is maximum on every induced component and the
bipartization number is additive across that exact disjoint decomposition. -/
def restrictedMaximumCutAndBetaAdditivityClaim47861 : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (c : V → Bool) (parts : Finset (Finset V)),
    maximumCut G c →
      componentPartition (crossingGraph G c) parts →
        (∀ P ∈ parts,
          maximumCut (inducedGraph G P) (fun v => c v.1)) ∧
        bipartizationNumber G =
          ∑ P ∈ parts, bipartizationNumber (inducedGraph G P)

/-- Claim 47862: the connected triangle-free quadratic bound transfers through
these exact components, while a global counterexample has a counterexample
component.  The displayed floor is the natural-number quotient. -/
def connectedTriangleFreeTransferClaim47862 : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (c : V → Bool) (parts : Finset (Finset V)),
    triangleFree G →
      maximumCut G c →
        componentPartition (crossingGraph G c) parts →
          ((∀ (W : Type*) [Fintype W] [DecidableEq W]
              (H : SimpleGraph W),
              H.Connected → triangleFree H →
                bipartizationNumber H ≤ Fintype.card W ^ 2 / 25) →
            bipartizationNumber G =
                ∑ P ∈ parts, bipartizationNumber (inducedGraph G P) ∧
              (∑ P ∈ parts, bipartizationNumber (inducedGraph G P)) ≤
                ∑ P ∈ parts, componentSize P ^ 2 / 25 ∧
              (∑ P ∈ parts, componentSize P ^ 2 / 25) ≤
                (∑ P ∈ parts, componentSize P ^ 2) / 25 ∧
              (∑ P ∈ parts, componentSize P ^ 2) / 25 ≤
                Fintype.card V ^ 2 / 25 ∧
              bipartizationNumber G ≤ Fintype.card V ^ 2 / 25) ∧
          (bipartizationNumber G > Fintype.card V ^ 2 / 25 →
            ∃ P ∈ parts,
              bipartizationNumber (inducedGraph G P) > componentSize P ^ 2 / 25)

end

end MathlibPlus.Open.GraphTheory.R3537
