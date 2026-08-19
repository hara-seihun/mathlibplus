import Mathlib
import MathlibPlus.Open.Research.FormalizationBatchUPolynomial
import MathlibPlus.Open.Research.FormalizationBatchCentroid

namespace MathlibPlus.Open.ResearchFormalization.R0353.Claim20302

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

/-- The genuine rooted factor before reversal. -/
def rootedROn {n : ℕ} (T : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (r : Fin n) : WPoly :=
  ∑ Q ∈ S.powerset.filter (rootedSubset T S r),
    Polynomial.C (forestUOn T (S \ Q)) * Polynomial.X ^ Q.card

/-- The factor `F_B=R_B+U_B` for an actual rooted branch. -/
def branchFactorOn {n : ℕ} (T : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (r : Fin n) : WPoly :=
  rootedROn T S r + Polynomial.C (forestUOn T S)

/-- Coefficient reversal at the stated order, i.e. the polynomial notation
`w^m p(w⁻¹)` used for a branch factor. -/
def reverseAt (m : ℕ) (p : WPoly) : WPoly :=
  ∑ k ∈ Finset.range (m + 1),
    Polynomial.C (p.coeff (m - k)) * Polynomial.X ^ k

/-- The exact centroid-core pruning expansion. -/
def centroidPruningZ {n : ℕ} (T : SimpleGraph (Fin n))
    (K : Finset (Fin n)) : WPoly :=
  ∑ C ∈ (Finset.univ : Finset (Fin n)).powerset.filter
      (fun C => K ⊆ C ∧ connectedSubset T C),
    Polynomial.C (forestUOn T ((Finset.univ : Finset (Fin n)) \ C)) *
      Polynomial.X ^ (n - C.card)

/-- The coefficient of `x_j` in a multivariate polynomial, retaining all
other variables in the coefficient polynomial. -/
def singleVariableCoeff (j : ℕ) (p : MPoly) : MPoly :=
  ∑ d ∈ p.support,
    if d j = 1 then MvPolynomial.monomial (d.erase j) (p.coeff d) else 0

/-- The unlabelled centroid core represented on the chosen finite carrier. -/
def centroidCoreFinset {n : ℕ} (T : SimpleGraph (Fin n)) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter
    (fun v => v ∈ MathlibPlus.Open.ResearchFormalizationBatch.centroidCore T)

/-- The marked derivative row of the centroid pruning polynomial. -/
def centroidJet {n : ℕ} (T : SimpleGraph (Fin n)) (k : ℕ) : MPoly :=
  MathlibPlus.Open.ResearchFormalizationBatch.partialXOne
    ((centroidPruningZ T (centroidCoreFinset T)).coeff k)

/-- A branch packet is exactly a finite family of connected components at the
supplied root: it covers every other vertex, is pairwise disjoint, has no
cross-edge, and meets the root only at its displayed attachment root. -/
def branchPacket {n : ℕ} (T : SimpleGraph (Fin n)) (c : Fin n)
    (bs : Finset (Finset (Fin n) × Fin n)) : Prop :=
  (∀ p ∈ bs,
    p.1.Nonempty ∧ p.2 ∈ p.1 ∧ connectedSubset T p.1 ∧ T.Adj c p.2) ∧
  (∀ p ∈ bs, ∀ v ∈ p.1, v ≠ c) ∧
  (∀ v : Fin n, v ≠ c → ∃ p, p ∈ bs ∧ v ∈ p.1) ∧
  (∀ p ∈ bs, ∀ q ∈ bs, p ≠ q → Disjoint p.1 q.1) ∧
  (∀ p ∈ bs, ∀ v ∈ p.1, T.Adj c v → v = p.2) ∧
  (∀ p ∈ bs, ∀ q ∈ bs, p ≠ q →
    ∀ u ∈ p.1, ∀ v ∈ q.1, ¬ T.Adj u v)

/-- The reversed product of the genuine branch factors. -/
def branchProduct {n : ℕ} (T : SimpleGraph (Fin n))
    (bs : Finset (Finset (Fin n) × Fin n)) : WPoly :=
  ∏ p ∈ bs, reverseAt p.1.card (branchFactorOn T p.1 p.2)

/-- The marked coefficient row of the branch product. -/
def branchJet {n : ℕ} (T : SimpleGraph (Fin n))
    (bs : Finset (Finset (Fin n) × Fin n)) (k : ℕ) : MPoly :=
  MathlibPlus.Open.ResearchFormalizationBatch.partialXOne
    ((branchProduct T bs).coeff k)

/-- The actual tree order's low truncation bound `ceil(n/2)`. -/
def halfCeil (n : ℕ) : ℕ := (n + 1) / 2

/-- The power-sum chromatic polynomial in its edge-subset expansion.  Its
`p₁` derivative is the unspecialized derivative denoted by `D(T)`. -/
def chromaticPowerPolynomial {n : ℕ} (T : SimpleGraph (Fin n)) : MPoly :=
  Finset.sum (Finset.powerset
      (MathlibPlus.Open.ResearchFormalizationBatch.uEdgeUniverse T))
    (fun A =>
      (-1 : MPoly) ^ A.card *
        Finset.prod
          (MathlibPlus.Open.ResearchFormalizationBatch.uComponents A)
          (fun C => MvPolynomial.X C.card))

def unspecializedDerivative {n : ℕ} (T : SimpleGraph (Fin n)) : MPoly :=
  MathlibPlus.Open.ResearchFormalizationBatch.partialXOne
    (chromaticPowerPolynomial T)

def uniqueCentroid {n : ℕ} (T : SimpleGraph (Fin n)) (c : Fin n) : Prop :=
  MathlibPlus.Open.ResearchFormalizationBatch.centroidCore T =
    ({c} : Set (Fin n))

/-- Claim 20302: the giant component coefficient row is the corresponding
low centroid-pruning derivative row, and equality of the unspecialized
`p₁` derivative determines every coefficient below `w^ceil(n/2)` of the
product of the reversed genuine centroid-branch factors. -/
def giantHalfSectorAndDetermination_claim20302 : Prop :=
  ∀ (n : ℕ) (T : SimpleGraph (Fin n)),
    T.IsTree →
    (∀ k : ℕ, 1 ≤ k → 2 * k < n →
      singleVariableCoeff (n - k)
          (MathlibPlus.Open.ResearchFormalizationBatch.markedSingletonPolynomial T) =
        centroidJet T k) ∧
    (∀ (T' : SimpleGraph (Fin n)) (c c' : Fin n)
        (bs bs' : Finset (Finset (Fin n) × Fin n)),
      T'.IsTree →
      uniqueCentroid T c → uniqueCentroid T' c' →
      branchPacket T c bs → branchPacket T' c' bs' →
      unspecializedDerivative T = unspecializedDerivative T' →
      ∀ k : ℕ, k < halfCeil n →
        branchJet T bs k = branchJet T' bs' k)

end
end MathlibPlus.Open.ResearchFormalization.R0353.Claim20302
