import Mathlib
import MathlibPlus.Open.FormalizationBatch.TreeCover
import MathlibPlus.Open.FormalizationBatch.R3134Claim47013Repair

namespace MathlibPlus.Open.FormalizationBatch.R3134Claim47016Repair

noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable
open Set

/-- The degree of a vertex in a finite simple graph, expressed without an
implicit finite-neighbor instance. -/
def vertexDegree {V : Type} [Fintype V] (T : SimpleGraph V) (v : V) : ℕ :=
  (T.neighborSet v).ncard

/-- The key used to list vertices of a rooted finite tree: distance from the
root, then degree inside the tree, then a finite display label. -/
def rootedSequenceKey {V : Type} [Fintype V]
    (T : SimpleGraph V) (r v : V) :
    ℕ × ℕ × Fin (Fintype.card V) :=
  (T.dist r v, vertexDegree T v, Fintype.equivFin V v)

/-- The displayed vertex list sorted by rooted distance and, within a layer,
by the degree sequence. -/
def rootedVertexSequence {V : Type} [Fintype V]
    (T : SimpleGraph V) (r : V) : List V :=
  List.mergeSort (Finset.univ : Finset V).toList
    (fun u v => decide (rootedSequenceKey T r u ≤ rootedSequenceKey T r v))

/-- The degree sequence of the displayed rooted vertex list. -/
def rootedDegreeSequence {V : Type} [Fintype V]
    (T : SimpleGraph V) (r : V) : List ℕ :=
  (rootedVertexSequence T r).map (vertexDegree T)

/-- The minimum of the rooted degree sequences over all roots. -/
noncomputable def minimumRootedSequence {V : Type} [Fintype V]
    (T : SimpleGraph V) : List ℕ :=
  let sequences :=
    (Finset.univ : Finset V).image (rootedDegreeSequence T)
  if h : sequences.Nonempty then sequences.min' h else []

/-- A root attaining the minimum rooted sequence, called a minimum leaf in the
packet's terminology. -/
def minimumLeaf {V : Type} [Fintype V]
    (T : SimpleGraph V) (r : V) : Prop :=
  rootedDegreeSequence T r = minimumRootedSequence T

/-- The graph-theoretic leaf condition used for the canonical attachment. -/
def graphLeaf {V : Type} [Fintype V]
    (T : SimpleGraph V) (v : V) : Prop :=
  (T.neighborSet v).Nonempty ∧ (T.neighborSet v).Subsingleton

/-- A child of `p` after rooting at `r`, expressed by the next distance layer. -/
def rootedChild {V : Type} [Fintype V]
    (T : SimpleGraph V) (r p c : V) : Prop :=
  T.Adj p c ∧ T.dist r c = T.dist r p + 1

/-- The children of a vertex in the rooting at `r`. -/
def rootedChildren {V : Type} [Fintype V]
    (T : SimpleGraph V) (r p : V) : Set V :=
  {c | rootedChild T r p c}

/-- The rooted child-star at `p`. -/
def rootedChildStar {V : Type} [Fintype V]
    (T : SimpleGraph V) (r p : V) : Set V :=
  {p} ∪ rootedChildren T r p

/-- The parent candidates of a nonroot vertex. -/
def parentCandidates {V : Type} [Fintype V]
    (T : SimpleGraph V) (r v : V) : Finset V :=
  (Finset.univ : Finset V).filter (fun p => rootedChild T r p v)

/-- A canonical parent choice; on a tree it is the unique neighbor in the
preceding rooted layer. -/
noncomputable def parentVertex {V : Type} [Fintype V]
    (T : SimpleGraph V) (r v : V) : V :=
  let candidates := parentCandidates T r v
  let labelled := candidates.image (Fintype.equivFin V)
  if h : labelled.Nonempty then
    (Fintype.equivFin V).symm (labelled.min' h)
  else r

/-- Labels in the envelope: `none` is the new top vertex and `some v` is the
old vertex `v`. -/
def envelopeParentLabel {V : Type} [Fintype V]
    (T : SimpleGraph V) (r v : V) : Option V :=
  if v = r then none else some (parentVertex T r v)

def envelopeVertexLabel {V : Type} (v : V) : Option V :=
  some v

/-- The edge label assigned to a source vertex by the rooted parent map. -/
def sourceEdgeLabel {V : Type} [Fintype V]
    (T : SimpleGraph V) (r v : V) : Sym2 (Option V) :=
  Sym2.mk (envelopeParentLabel T r v) (envelopeVertexLabel v)

/-- The tree obtained by adding the top vertex above the old root. -/
def attachedEnvelopeGraph {V : Type} [Fintype V]
    (T : SimpleGraph V) (r : V) : SimpleGraph (Option V) :=
  SimpleGraph.fromRel (fun x y =>
    (∃ u v : V, T.Adj u v ∧ x = envelopeVertexLabel u ∧
      y = envelopeVertexLabel v) ∨
      (x = none ∧ y = envelopeVertexLabel r))

/-- The cover indexed by the envelope vertices: old vertices index their
rooted child-stars and the new top vertex indexes the singleton `{r}`. -/
def canonicalChildStarCover {V : Type} [Fintype V]
    (T : SimpleGraph V) (r : V) : Option V → Set V
  | none => {r}
  | some v => rootedChildStar T r v

/-- Minimality of an envelope, using the rooted sequence minimum from the
packet and allowing every finite carrier for competing envelopes. -/
def minimalEnvelope {V : Type} [Fintype V]
    (T : SimpleGraph V) (H : SimpleGraph (Option V)) : Prop :=
  MathlibPlus.Open.FormalizationBatch.R3134Claim47013Repair.lineTreeEnvelope
      T H ∧
    ∀ {A : Type} [Fintype A] (K : SimpleGraph A),
      MathlibPlus.Open.FormalizationBatch.R3134Claim47013Repair.lineTreeEnvelope
        T K →
        minimumRootedSequence H ≤ minimumRootedSequence K

/-- Claim 47016: a minimum-leaf rooting gives the canonical leaf attachment,
its parent-edge map is a line-tree envelope, and the dual exact cover is the
rooted child-star family with the top singleton. -/
def claim47016 : Prop :=
  ∀ {V : Type} [Fintype V] (T : SimpleGraph V),
    2 ≤ Fintype.card V → T.IsTree →
      ∃ (a₁ : V) (H : SimpleGraph (Option V))
        (β : V ≃ H.edgeSet),
        minimumLeaf T a₁ ∧
          graphLeaf T a₁ ∧
            H = attachedEnvelopeGraph T a₁ ∧
              H.IsTree ∧
                minimalEnvelope T H ∧
                  (∀ v : V,
                    v ≠ a₁ →
                      rootedChild T a₁ (parentVertex T a₁ v) v) ∧
                    (∀ v : V,
                      (β v : Sym2 (Option V)) = sourceEdgeLabel T a₁ v) ∧
                  MathlibPlus.Open.FormalizationBatch.R3134Claim47013Repair.lineTreeEnvelopeWithMap
                    T H β ∧
                    (let C := canonicalChildStarCover T a₁
                     MathlibPlus.Open.FormalizationBatch.TreeCover.exactConnected2Cover T C ∧
                       H =
                         MathlibPlus.Open.FormalizationBatch.R3134Claim47013Repair.dualIncidenceGraph
                           C ∧
                         MathlibPlus.Open.FormalizationBatch.R3134Claim47013Repair.incidenceMap
                           C H β ∧
                         MathlibPlus.Open.FormalizationBatch.R3134Claim47013Repair.coverEnvelopePresentation
                           T C)

end

end MathlibPlus.Open.FormalizationBatch.R3134Claim47016Repair
