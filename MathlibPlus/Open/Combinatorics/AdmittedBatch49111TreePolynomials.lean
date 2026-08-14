import Mathlib

open scoped BigOperators Classical

namespace MathlibPlus.Open.Combinatorics.AdmittedBatch49111

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Connectivity of a nonempty vertex set in the graph induced by the set. -/
def connectedSubset (T : SimpleGraph V) (S : Finset V) : Prop :=
  S.Nonempty ∧
    ∀ x ∈ S, ∀ y ∈ S,
      Relation.ReflTransGen
        (fun a b : V => a ∈ S ∧ b ∈ S ∧ T.Adj a b) x y

def vertexDegree (T : SimpleGraph V) (z : V) : ℕ :=
  (Finset.univ.filter (fun w => T.Adj z w)).card

def edgeBoundary (T : SimpleGraph V) (S : Finset V) : ℕ :=
  S.sum (fun x => ((Finset.univ : Finset V).filter
    (fun y => T.Adj x y ∧ y ∉ S)).card)

def UPolynomial (T : SimpleGraph V) (u v : Polynomial ℚ) : Polynomial ℚ :=
  ∑ S : Finset V,
    if connectedSubset T S then
      u ^ (S.card - 1) * v ^ edgeBoundary T S
    else 0

def avoidingPolynomial (T : SimpleGraph V) (r : V)
    (u v : Polynomial ℚ) : Polynomial ℚ :=
  ∑ S : Finset V,
    if connectedSubset T S ∧ r ∉ S then
      u ^ (S.card - 1) * v ^ edgeBoundary T S
    else 0

def containingPolynomial (T : SimpleGraph V) (r : V)
    (u v : Polynomial ℚ) : Polynomial ℚ :=
  ∑ S : Finset V,
    if connectedSubset T S ∧ r ∈ S then
      u ^ (S.card - 1) * v ^ edgeBoundary T S
    else 0

def avoidingNontrivialPolynomial (T : SimpleGraph V) (r : V)
    (u v : Polynomial ℚ) : Polynomial ℚ :=
  ∑ S : Finset V,
    if connectedSubset T S ∧ r ∉ S ∧ 2 ≤ S.card then
      u ^ (S.card - 1) * v ^ edgeBoundary T S
    else 0

/-- R-3875 S1: the connected-set polynomial and its root split. -/
def uPolynomialRootSplit : Prop :=
  ∀ (T : SimpleGraph V) (r : V) (u v : Polynomial ℚ), T.IsTree →
    UPolynomial T u v = containingPolynomial T r u v + avoidingPolynomial T r u v

/-- The singleton layer omitted from the nontrivial avoiding polynomial. -/
def singletonAvoidingLayer (T : SimpleGraph V) (r : V)
    (v : Polynomial ℚ) : Polynomial ℚ :=
  ∑ z : V, if z ≠ r then v ^ vertexDegree T z else 0

/-- R-3875 S2: exact singleton deletion and the equal-degree consequence. -/
def singletonLayerIdentity : Prop :=
  ∀ (T : SimpleGraph V) (r : V) (u v : Polynomial ℚ), T.IsTree →
    avoidingPolynomial T r u v - avoidingNontrivialPolynomial T r u v =
      singletonAvoidingLayer T r v ∧
    ∀ s : V, vertexDegree T r = vertexDegree T s →
      singletonAvoidingLayer T r v = singletonAvoidingLayer T s v

/-- The census of connected avoiding sets with prescribed size and boundary. -/
def avoidingCensus (T : SimpleGraph V) (r : V) (k b : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset V)).filter
    (fun S => connectedSubset T S ∧ r ∉ S ∧ S.card = k ∧
      edgeBoundary T S = b)).card

def rootedGraphIsomorphism (T : SimpleGraph V) (r s : V) : Prop :=
  ∃ e : V ≃ V, e r = s ∧ ∀ x y : V,
    T.Adj x y ↔ T.Adj (e x) (e y)

/-- R-3875 S3: equality of all nontrivial avoiding censuses gives a rooted isomorphism. -/
def avoidingCensusRigidity : Prop :=
  ∀ (T : SimpleGraph V) (r s : V), T.IsTree →
    vertexDegree T r = vertexDegree T s →
    (∀ k b : ℕ, 2 ≤ k → avoidingCensus T r k b = avoidingCensus T s k b) →
    rootedGraphIsomorphism T r s

end

end MathlibPlus.Open.Combinatorics.AdmittedBatch49111
