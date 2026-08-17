import MathlibPlus.Open.LinearAlgebra.AcyclicRelationRows

namespace MathlibPlus.Open.LinearAlgebra.R0875Claim25527

noncomputable section
open scoped BigOperators
open Classical

/-- An oriented multigraph incidence entry; edge labels are retained, so
parallel edges are distinct columns. -/
def orientedIncidence {K V E : Type*} [Field K] [DecidableEq V]
    (src tgt : E → V) (v : V) (e : E) : K :=
  if tgt e = v then 1 else if src e = v then -1 else 0

def multigraphAdj {V E : Type*} (src tgt : E → V) (u v : V) : Prop :=
  ∃ e, (src e = u ∧ tgt e = v) ∨ (src e = v ∧ tgt e = u)

def componentRootSet {V E : Type*} [Fintype V]
    (src tgt : E → V) (roots : Set V) : Prop :=
  (∀ v : V, ∃ r, r ∈ roots ∧
    Relation.ReflTransGen (multigraphAdj src tgt) v r) ∧
    (∀ r ∈ roots, ∀ r' ∈ roots,
      Relation.ReflTransGen (multigraphAdj src tgt) r r' → r = r')

abbrev reducedVertex {V : Type*} (roots : Set V) := {v : V // v ∉ roots}

def reducedIncidence {K V E : Type*} [Field K] [DecidableEq V]
    (src tgt : E → V) (roots : Set V) :
    Matrix (reducedVertex roots) E K :=
  fun v e => orientedIncidence src tgt v.1 e

def diagonalScaling {K E : Type*} [Field K] [DecidableEq E]
    (s : E → K) : Matrix E E K :=
  fun e f => if e = f then s e else 0

def weightedReducedIncidence {K V E : Type*} [Field K]
    [Fintype E] [DecidableEq V] [DecidableEq E]
    (src tgt : E → V) (roots : Set V) (s : E → K) :
    Matrix (reducedVertex roots) E K :=
  reducedIncidence (K := K) src tgt roots * diagonalScaling (K := K) s

/-- The exact constructed graph/cycle data, not an arbitrary incidence matrix. -/
def fundamentalCycleRealization
    {K R E V : Type*} [Field K]
    [Fintype R] [Fintype E] [Fintype V]
    [DecidableEq E] [DecidableEq V]
    (support : R → Finset E) (coeff c : R → E → K)
    (src tgt : E → V) (roots : Set V) : Prop :=
  relationCoordinateIncidenceForest support coeff ∧
    componentRootSet src tgt roots ∧
    (∀ e : E, src e ≠ tgt e) ∧
    (∀ α e, e ∈ support α → (c α e = 1 ∨ c α e = -1)) ∧
    (∀ α e, c α e = 0 ↔ e ∉ support α) ∧
    (∀ α v, ∑ e : E, orientedIncidence src tgt v e * c α e = 0) ∧
    LinearIndependent K c ∧
    (∀ z : E → K,
      (∀ v, ∑ e : E, orientedIncidence src tgt v e * z e = 0) →
        ∃ q : R → K, ∀ e, z e = ∑ α, q α * c α e)

def relationRowSpan {K R E : Type*} [Field K]
    [Fintype R] [DecidableEq E]
    (support : R → Finset E) (coeff : R → E → K) :
    Submodule K (E → K) :=
  Submodule.span K (Set.range (relationRow support coeff))

/-- The scaling is the one transported from the constructed fundamental
cycles, not a free replacement for the relation coefficients. -/
def coefficientTransport {K R E : Type*} [Field K]
    [Fintype R] [DecidableEq E]
    (support : R → Finset E) (coeff c : R → E → K)
    (t : R → K) (s : E → K) : Prop :=
  (∀ α, t α ≠ 0) ∧ (∀ e, s e ≠ 0) ∧
    (∀ α e, e ∈ support α →
      s e * coeff α e = t α * c α e)

/-- Claim 25527: the kernel of the concrete weighted reduced incidence map is
exactly the row span of the relation matrix, and the reduced incidence has the
codimension forced by the independent forest rows. -/
def exactWeightedGraphicKernel_claim25527 : Prop :=
  ∀ {K R E V : Type*} [Field K]
    [Fintype R] [Fintype E] [Fintype V]
    [DecidableEq E] [DecidableEq V]
    (support : R → Finset E) (coeff c : R → E → K)
    (src tgt : E → V) (roots : Set V)
    (t : R → K) (s : E → K),
    fundamentalCycleRealization (K := K) support coeff c src tgt roots →
      coefficientTransport (K := K) support coeff c t s →
      LinearMap.ker
          (Matrix.mulVecLin
            (weightedReducedIncidence (K := K) src tgt roots s)) =
        relationRowSpan (K := K) support coeff ∧
      Matrix.rank (reducedIncidence (K := K) src tgt roots) =
        Fintype.card E - Fintype.card R

end

end MathlibPlus.Open.LinearAlgebra.R0875Claim25527
