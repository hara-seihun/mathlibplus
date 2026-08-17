import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch.UPolynomial

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Claim22342IndependentDeletionRealizability

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

private abbrev UPolynomial := MvPolynomial ℕ ℤ
private abbrev ShiftedPolynomial := MvPolynomial (Option ℕ) ℤ

private def deletedVertices {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (S : Finset V) : SimpleGraph {v // v ∉ S} :=
  F.induce {v : V | v ∉ S}

private noncomputable def deletedUPolynomial {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (S : Finset V) : UPolynomial :=
  letI := Fintype.ofFinite (↥(deletedVertices F S).edgeSet)
  MvPolynomial.map (Nat.castRingHom ℤ)
    (MathlibPlus.Open.ResearchFormalizationBatch.graphUPolynomial
      (deletedVertices F S))

private def independentVertexSet {V : Type*} [DecidableEq V]
    (F : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, u ∈ S → v ∈ S → u ≠ v → ¬ F.Adj u v

private def renameUToY (p : UPolynomial) : ShiftedPolynomial :=
  MvPolynomial.rename (fun n : ℕ => some n) p

private def shiftedRootFactor {V : Type*} [Fintype V] [DecidableEq V]
    (B : SimpleGraph V) (r : V) : ShiftedPolynomial :=
  ∑ I ∈ ((Finset.univ : Finset V).powerset).filter (fun I =>
      independentVertexSet B I ∧ r ∉ I),
    (-MvPolynomial.X none) ^ I.card *
      renameUToY (deletedUPolynomial B I)

private def ordinaryYDegree (a : (Option ℕ) →₀ ℕ) : ℕ :=
  a.sum (fun i e => match i with | none => 0 | some _ => e)

private def ordinaryYDegreeOne (p : ShiftedPolynomial) : ShiftedPolynomial :=
  ∑ a ∈ p.support.filter (fun a => ordinaryYDegree a = 1),
    MvPolynomial.monomial a (MvPolynomial.coeff a p)

private def leafCount {V : Type*} [Fintype V] [DecidableEq V]
    (B : SimpleGraph V) (r : V) : ℕ :=
  (Finset.univ.filter (fun v => v ≠ r ∧ B.degree v = 1)).card

private def leafLayerForm {V : Type*} [Fintype V] [DecidableEq V]
    (B : SimpleGraph V) (r : V) : ShiftedPolynomial :=
  ∑ k ∈ Finset.range (leafCount B r + 1),
    (Nat.choose (leafCount B r) k : ℤ) •
      ((-MvPolynomial.X none) ^ k *
        MvPolynomial.X (some (Fintype.card V - k)))

private def pathGraph (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun i j =>
    i.1 + 1 = j.1 ∨ j.1 + 1 = i.1)

private def endpointPathFactor : ShiftedPolynomial :=
  shiftedRootFactor (pathGraph 7) (0 : Fin 7)

private def endpointLinearForm : ShiftedPolynomial :=
  MvPolynomial.X (some 7) -
    MvPolynomial.X none * MvPolynomial.X (some 6)

private def shiftedH : ShiftedPolynomial :=
  MvPolynomial.X none ^ 2 * MvPolynomial.X (some 5) -
    MvPolynomial.X none ^ 5 * MvPolynomial.X (some 2)

private def shiftedK : ShiftedPolynomial :=
  MvPolynomial.X none ^ 3 * MvPolynomial.X (some 4) -
    MvPolynomial.X none ^ 4 * MvPolynomial.X (some 3)

private def ambientG00 : ShiftedPolynomial :=
  endpointPathFactor

private def ambientG10 : ShiftedPolynomial :=
  endpointPathFactor + shiftedH

private def ambientG01 : ShiftedPolynomial :=
  endpointPathFactor + shiftedK

private def ambientG11 : ShiftedPolynomial :=
  endpointPathFactor + shiftedH + shiftedK

private def leafLayerRealizable (P : ShiftedPolynomial) : Prop :=
  ∃ (V : Type) (fV : Fintype V) (dV : DecidableEq V)
    (B : SimpleGraph V) (r : V),
    B.IsTree ∧
      @leafLayerForm V fV dV B r = ordinaryYDegreeOne P

private def genuineFactor (P : ShiftedPolynomial) : Prop :=
  ∃ (V : Type) (fV : Fintype V) (dV : DecidableEq V)
    (B : SimpleGraph V) (r : V),
    B.IsTree ∧ @shiftedRootFactor V fV dV B r = P

private def genuineQuartet : Prop :=
  genuineFactor ambientG00 ∧ genuineFactor ambientG10 ∧
    genuineFactor ambientG01 ∧ genuineFactor ambientG11

private def ambientCollision : Prop :=
  MvPolynomial.pderiv (some 1) (ambientG00 * ambientG11) =
      MvPolynomial.pderiv (some 1) (ambientG10 * ambientG01) ∧
    ambientG00 * ambientG11 - ambientG10 * ambientG01 ≠ 0

private def ambientSIDCounterexample : Prop :=
  genuineQuartet ∧ ambientCollision

/-- Claim 22342: the independent-deletion first layer rules out the ambient
quartet as a quartet of genuine rooted-tree factors, despite its displayed
shifted perturbation, so it is not an SID counterexample. -/
def claim22342 : Prop :=
  ordinaryYDegreeOne endpointPathFactor = endpointLinearForm ∧
    ordinaryYDegreeOne ambientG10 = endpointLinearForm + shiftedH ∧
    ¬ leafLayerRealizable ambientG10 ∧
    ambientCollision ∧
    ¬ genuineQuartet ∧
    ¬ ambientSIDCounterexample

end

end MathlibPlus.Open.ResearchFormalization.Claim22342IndependentDeletionRealizability
