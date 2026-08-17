import MathlibPlus.Open.LinearAlgebra.AcyclicRelationRows

namespace MathlibPlus.Open.LinearAlgebra.R0875Claim25528

noncomputable section
open scoped BigOperators
open Classical

/-- The oriented incidence column of the constructed multigraph. -/
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

/-- The rooted graph and its fundamental cycles are fixed by the relation
supports; this predicate records their actual flow and basis properties. -/
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

abbrev commonQuotient {K R E : Type*} [Field K]
    [Fintype R] [DecidableEq E]
    (support : R → Finset E) (coeff : R → E → K) : Type _ :=
  (E → K) ⧸ relationRowSpan support coeff

def quotientCoordinate {K R E : Type*} [Field K]
    [Fintype R] [DecidableEq E]
    (support : R → Finset E) (coeff : R → E → K) (e : E) :
    commonQuotient support coeff :=
  (relationRowSpan support coeff).mkQ (Pi.single e 1)

def quotientRow {K V E : Type*} [Field K]
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (src tgt : E → V) (roots : Set V) (s : E → K)
    (v : reducedVertex roots) : E → K :=
  fun e => weightedReducedIncidence (K := K) src tgt roots s v e

/-- Support size of a column in the actual reduced incidence matrix. -/
def reducedColumnSupport {K V E : Type*} [Field K]
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (src tgt : E → V) (roots : Set V) (s : E → K) (e : E) : ℕ :=
  (Finset.univ.filter (fun v : reducedVertex roots =>
    weightedReducedIncidence (K := K) src tgt roots s v e ≠ 0)).card

def coefficientTransport {K R E : Type*} [Field K]
    [Fintype R] [DecidableEq E]
    (support : R → Finset E) (coeff c : R → E → K)
    (t : R → K) (s : E → K) : Prop :=
  (∀ α, t α ≠ 0) ∧ (∀ e, s e ≠ 0) ∧
    (∀ α e, e ∈ support α →
      s e * coeff α e = t α * c α e)

/-- The rows of `D_Γ S` descend to the quotient as the proposed common
basis, while the induced quotient map sends a coordinate to its genuine
scaled incidence column. -/
def commonWidthTwoQuotient_claim25528 : Prop :=
  ∀ {K R E V : Type*} [Field K]
    [Fintype R] [Fintype E] [Fintype V]
    [DecidableEq E] [DecidableEq V]
    (support : R → Finset E) (coeff c : R → E → K)
    (src tgt : E → V) (roots : Set V)
    (t : R → K) (s : E → K),
    fundamentalCycleRealization (K := K) support coeff c src tgt roots →
      coefficientTransport (K := K) support coeff c t s →
      ∃ (b : Module.Basis (reducedVertex roots) K
          (commonQuotient support coeff))
        (φ : commonQuotient support coeff →ₗ[K]
          (reducedVertex roots → K)),
        (∀ v, b v =
          (relationRowSpan support coeff).mkQ
            (quotientRow src tgt roots s v)) ∧
        Function.Injective φ ∧
        (∀ z : E → K,
          φ ((relationRowSpan support coeff).mkQ z) =
            (Matrix.mulVecLin
              (weightedReducedIncidence (K := K) src tgt roots s)) z) ∧
        (∀ e,
          1 ≤ (Finset.univ.filter (fun v : reducedVertex roots =>
            φ ((relationRowSpan support coeff).mkQ (Pi.single e 1)) v ≠ 0)).card ∧
          (Finset.univ.filter (fun v : reducedVertex roots =>
            φ ((relationRowSpan support coeff).mkQ (Pi.single e 1)) v ≠ 0)).card ≤ 2) ∧
        (∀ e, 1 ≤ reducedColumnSupport src tgt roots s e ∧
          reducedColumnSupport src tgt roots s e ≤ 2)

end

end MathlibPlus.Open.LinearAlgebra.R0875Claim25528
