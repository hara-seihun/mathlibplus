import Mathlib
import MathlibPlus.GraphTheory.Claim28295

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.Research.R0333

abbrev PteVertex (α m : ℕ) := Unit ⊕ (Fin m × (Unit ⊕ (Fin α × Fin 3)))

def pteCenter {α m : ℕ} : PteVertex α m :=
  Sum.inl ()

def pteBranchRoot {α m : ℕ} (i : Fin m) : PteVertex α m :=
  Sum.inr (i, Sum.inl ())

def pteArmVertex {α m : ℕ} (i : Fin m) (j : Fin α) (k : Fin 3) : PteVertex α m :=
  Sum.inr (i, Sum.inr (j, k))

def pteEdge {V : Type*} (u v : V) : Sym2 V :=
  Sym2.mk u v

def ptePathArmEdges {α m : ℕ} (i : Fin m) (j : Fin α) :
    Finset (Sym2 (PteVertex α m)) :=
  {pteEdge (pteBranchRoot i) (pteArmVertex i j 0),
    pteEdge (pteArmVertex i j 0) (pteArmVertex i j 1),
    pteEdge (pteArmVertex i j 1) (pteArmVertex i j 2)}

def pteStarArmEdges {α m : ℕ} (i : Fin m) (j : Fin α) :
    Finset (Sym2 (PteVertex α m)) :=
  {pteEdge (pteBranchRoot i) (pteArmVertex i j 0),
    pteEdge (pteBranchRoot i) (pteArmVertex i j 1),
    pteEdge (pteBranchRoot i) (pteArmVertex i j 2)}

def pteEdges (α m : ℕ) (p : Fin m → ℕ) :
    Finset (Sym2 (PteVertex α m)) :=
  (Finset.univ : Finset (Fin m)).biUnion (fun i =>
    {pteEdge pteCenter (pteBranchRoot i)} ∪
      (Finset.univ : Finset (Fin α)).biUnion (fun j =>
        if j.val < p i then ptePathArmEdges i j else pteStarArmEdges i j))

def pteGraph (α m : ℕ) (p : Fin m → ℕ) : SimpleGraph (PteVertex α m) :=
  SimpleGraph.fromEdgeSet (pteEdges α m p : Set (Sym2 (PteVertex α m)))

def pteCompatible (α m : ℕ) (p : Fin m → ℕ) : Prop :=
  2 ≤ m ∧ ∀ i : Fin m, 0 ≤ p i ∧ p i ≤ α

def pteOrder (α m : ℕ) : ℕ :=
  m * (3 * α + 1) + 1

def multisetExponent (part : Multiset ℕ) : ℕ →₀ ℕ :=
  (part.map (fun k => Finsupp.single k 1)).sum

def partitionMonomial (part : Multiset ℕ) : MvPolynomial ℕ ℚ :=
  (part.map (fun k => MvPolynomial.X k)).prod

def graphEdgeFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finset (Sym2 V) :=
  letI : DecidablePred (fun e : Sym2 V => e ∈ G.edgeSet) :=
    fun e => Classical.propDecidable (e ∈ G.edgeSet)
  (Finset.univ : Finset (Sym2 V)).filter (fun e => e ∈ G.edgeSet)

def cutPolynomial {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : MvPolynomial ℕ ℚ :=
  ∑ E ∈ (graphEdgeFinset G).powerset,
    (-1 : ℚ) ^ E.card •
      partitionMonomial
        (MathlibPlus.GraphTheory.Claim28295.componentSizes
          (SimpleGraph.fromEdgeSet (E : Set (Sym2 V))))

def deckSum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : MvPolynomial ℕ ℚ :=
  MvPolynomial.pderiv 1 (cutPolynomial G)

def deckCoefficient {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (part : Multiset ℕ) : ℚ :=
  MvPolynomial.coeff (multisetExponent part) (deckSum G)

def singletonPartition (α m k : ℕ) : Multiset ℕ :=
  {pteOrder α m - 3 * α - 1, 3 * α - 2 * k} + Multiset.replicate k 2

def branchContribution (α k p : ℕ) : ℚ :=
  (2 * (α : ℚ) - (p : ℚ) + (k : ℚ)) * (Nat.choose p k : ℚ) +
    2 * ((α : ℚ) - (p : ℚ)) * (Nat.choose p (k - 1) : ℚ)

def claim19995 : Prop :=
  ∀ (α m : ℕ) (p : Fin m → ℕ) (k : ℕ),
    pteCompatible α m p → 1 ≤ k → k < α →
    let N := pteOrder α m
    let μ := singletonPartition α m k
    (-1 : ℚ) ^ (N - k - 3) * deckCoefficient (pteGraph α m p) μ =
      ∑ i : Fin m, branchContribution α k (p i)

def sequenceMultiset {m : ℕ} (p : Fin m → ℕ) : Multiset ℕ :=
  (Finset.univ : Finset (Fin m)).val.map p

def pteDeckSum (α m : ℕ) (p : Fin m → ℕ) : MvPolynomial ℕ ℚ :=
  deckSum (pteGraph α m p)

def pteTreeIsomorphic (α m α' m' : ℕ)
    (p : Fin m → ℕ) (p' : Fin m' → ℕ) : Prop :=
  ∃ e : PteVertex α m ≃ PteVertex α' m',
    ∀ u v,
      (pteGraph α m p).Adj u v ↔ (pteGraph α' m' p').Adj (e u) (e v)

def claim19999 : Prop :=
  ∀ (α m α' m' : ℕ) (p : Fin m → ℕ) (p' : Fin m' → ℕ),
    pteCompatible α m p → pteCompatible α' m' p' →
    pteDeckSum α m p = pteDeckSum α' m' p' →
      α = α' ∧ m = m' ∧ sequenceMultiset p = sequenceMultiset p' ∧
        pteTreeIsomorphic α m α' m' p p'

def edgeCutCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (part : Multiset ℕ) : ℕ :=
  Finset.filter (fun A : Finset (Sym2 V) =>
    MathlibPlus.GraphTheory.Claim28295.componentSizes
        (G.deleteEdges (A : Set (Sym2 V))) = part)
    ((graphEdgeFinset G).powerset) |>.card

def pteSequence11 : Fin 2 → ℕ :=
  fun _ => 1

def pteSequence20 : Fin 2 → ℕ :=
  fun i => if i = 0 then 2 else 0

def pteSequence2220 : Fin 4 → ℕ :=
  fun i => if i.val < 3 then 2 else 0

def pteSequence3111 : Fin 4 → ℕ :=
  fun i => if i = 0 then 3 else 1

def claim20000 : Prop :=
  edgeCutCount (pteGraph 2 2 pteSequence11)
      (singletonPartition 2 2 1 + {1}) = 12 ∧
    edgeCutCount (pteGraph 2 2 pteSequence20)
      (singletonPartition 2 2 1 + {1}) = 10 ∧
    edgeCutCount (pteGraph 3 4 pteSequence2220)
      (singletonPartition 3 4 2 + {1}) = 30 ∧
    edgeCutCount (pteGraph 3 4 pteSequence3111)
      (singletonPartition 3 4 2 + {1}) = 27

end MathlibPlus.Open.Research.R0333
end
