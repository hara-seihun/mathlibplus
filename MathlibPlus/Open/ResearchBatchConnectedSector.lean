import Mathlib

namespace MathlibPlus.Open.ResearchBatchConnectedSector

noncomputable section
open Classical
open scoped BigOperators

abbrev BivariatePolynomial := Polynomial (Polynomial ℤ)

def complementGraphComponentCount {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (A : Finset V) : ℕ :=
  Fintype.card (SimpleGraph.ConnectedComponent
    (T.induce (↑(Aᶜ) : Set V)))

def connectedInduced {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (A : Finset V) : Prop :=
  A.Nonempty ∧ (T.induce (↑A : Set V)).Connected

def connectedSubsets {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) : Finset (Finset V) :=
  (Finset.univ.powerset).filter (connectedInduced T)

def sectorMonomial {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (A : Finset V) : BivariatePolynomial :=
  Polynomial.monomial (Fintype.card V - A.card)
    (Polynomial.monomial (complementGraphComponentCount T A) 1)

def connectedSectorK {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) : BivariatePolynomial :=
  ∑ A ∈ connectedSubsets T, sectorMonomial T A

def vertexRootedSector {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) : BivariatePolynomial :=
  ∑ A ∈ connectedSubsets T, A.card • sectorMonomial T A

def undirectedEdgeRootedSector {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) : BivariatePolynomial :=
  ∑ A ∈ connectedSubsets T, (A.card - 1) • sectorMonomial T A

def directedEdgeRootedSector {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) : BivariatePolynomial :=
  ∑ A ∈ connectedSubsets T, 2 • ((A.card - 1) • sectorMonomial T A)

def outerWDerivative {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) : BivariatePolynomial :=
  Polynomial.X * Polynomial.derivative (connectedSectorK T)

/-- The exact one-colour connected-sector identities for a finite tree. -/
def oneColourConnectedSectorIdentities : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (T : SimpleGraph V), T.IsTree →
    vertexRootedSector T = Fintype.card V • connectedSectorK T - outerWDerivative T ∧
      undirectedEdgeRootedSector T =
        Fintype.card V • connectedSectorK T - outerWDerivative T - connectedSectorK T ∧
      directedEdgeRootedSector T = 2 • undirectedEdgeRootedSector T

end
end MathlibPlus.Open.ResearchBatchConnectedSector
