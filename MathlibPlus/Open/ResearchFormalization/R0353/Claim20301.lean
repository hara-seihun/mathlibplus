import Mathlib
import MathlibPlus.Open.Research.FormalizationBatchUPolynomial
import MathlibPlus.Open.Research.FormalizationBatchCentroid

namespace MathlibPlus.Open.ResearchFormalization.R0353.Claim20301

noncomputable section
open Classical
open scoped BigOperators

abbrev MPoly := MvPolynomial ℕ ℤ
abbrev WPoly := Polynomial MPoly

/-- The induced graph carried by a finite vertex subset. -/
def inducedGraph {n : ℕ} (T : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : SimpleGraph {v // v ∈ S} :=
  T.induce (S : Set (Fin n))

/-- The component-size polynomial of the induced graph on a finite subset. -/
def forestUOn {n : ℕ} (T : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : MPoly :=
  MathlibPlus.Open.ResearchFormalizationBatch.forestUPolynomial
    (inducedGraph T S)

def connectedSubset {n : ℕ} (T : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : Prop :=
  S.Nonempty ∧
    MathlibPlus.Open.ResearchFormalizationBatch.inducesConnected T S

def rootedSubset {n : ℕ} (T : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (r : Fin n) (Q : Finset (Fin n)) : Prop :=
  Q.Nonempty ∧ Q ⊆ S ∧ r ∈ Q ∧
    MathlibPlus.Open.ResearchFormalizationBatch.inducesConnected T Q

/-- The genuine rooted polynomial, with the root-containing connected set as
its z-marked part and the component-size U-polynomial on the complement. -/
def rootedROn {n : ℕ} (T : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (r : Fin n) : WPoly :=
  ∑ Q ∈ S.powerset.filter (rootedSubset T S r),
    Polynomial.C (forestUOn T (S \ Q)) * Polynomial.X ^ Q.card

/-- The centroid-core pruning polynomial. -/
def centroidPruningZ {n : ℕ} (T : SimpleGraph (Fin n))
    (K : Finset (Fin n)) : WPoly :=
  ∑ C ∈ (Finset.univ : Finset (Fin n)).powerset.filter
      (fun C => K ⊆ C ∧ connectedSubset T C),
    Polynomial.C (forestUOn T ((Finset.univ : Finset (Fin n)) \ C)) *
      Polynomial.X ^ (n - C.card)

/-- Coefficient reversal at the stated order, i.e. the polynomial notation
`w^n p(w⁻¹)` used in the claim. -/
def reverseAt (n : ℕ) (p : WPoly) : WPoly :=
  ∑ k ∈ Finset.range (n + 1),
    Polynomial.C (p.coeff (n - k)) * Polynomial.X ^ k

/-- A labelled tree has the stated unique centroid when its centroid core is
exactly the singleton containing the supplied vertex. -/
def uniqueCentroid {n : ℕ} (T : SimpleGraph (Fin n)) (c : Fin n) : Prop :=
  MathlibPlus.Open.ResearchFormalizationBatch.centroidCore T =
    ({c} : Set (Fin n))

/-- Claim 20301: the centroid pruning polynomial is the reversal of the
rooted polynomial at its unique centroid. -/
def uniqueCentroidPruningProductReversal_claim20301 : Prop :=
  ∀ (n : ℕ) (T : SimpleGraph (Fin n)) (c : Fin n),
    T.IsTree →
    uniqueCentroid T c →
      centroidPruningZ T ({c} : Finset (Fin n)) =
        reverseAt n (rootedROn T (Finset.univ : Finset (Fin n)) c)

end
end MathlibPlus.Open.ResearchFormalization.R0353.Claim20301
