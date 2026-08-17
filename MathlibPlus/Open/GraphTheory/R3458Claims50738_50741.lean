import Mathlib

namespace MathlibPlus.Open.GraphTheory.R3458Claims50738_50741

noncomputable section

/-- The number of common neighbours of an ordered pair in a finite simple
    graph. -/
noncomputable def commonNeighborCount {V : Type*} [Fintype V]
    (G : SimpleGraph V) (u w : V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun v => G.Adj u v ∧ G.Adj w v)).card

/-- The common-neighbour value set used by the no-consecutive hypothesis. -/
def commonNeighborValueSet {V : Type*} [Fintype V]
    (G : SimpleGraph V) : Set ℕ :=
  {c | ∃ u w : V, u ≠ w ∧ commonNeighborCount G u w = c}

/-- No two members of a set are consecutive. -/
def noConsecutiveValues (S : Set ℕ) : Prop :=
  ∀ c : ℕ, c ∈ S → c + 1 ∉ S

/-- The card isomorphism on the surviving vertices, written as its extension
    to the common label type.  The extension fixes the deleted label. -/
def offVertexCardIso {V : Type*}
    (G H : SimpleGraph V) (i : V) (π : Equiv.Perm V) : Prop :=
  π i = i ∧
    ∀ x y : V, x ≠ i → y ≠ i →
      (G.Adj x y ↔ H.Adj (π x) (π y))

/-- The source attachment indicator a_u = 1_{iu in E(G)}. -/
noncomputable def sourceAttachmentBit {V : Type*}
    (G : SimpleGraph V) (i u : V) : ℕ := by
  classical
  exact if G.Adj i u then 1 else 0

/-- The target attachment indicator b_u = 1_{i π(u) in E(H)}, indexed by
    the surviving source labels. -/
noncomputable def targetAttachmentBit {V : Type*}
    (H : SimpleGraph V) (i : V) (π : Equiv.Perm V) (u : V) : ℕ := by
  classical
  exact if H.Adj i (π u) then 1 else 0

/-- The two attachment products in the deletion identity. -/
def sourceAttachmentProduct {V : Type*}
    (G : SimpleGraph V) (i u w : V) : ℕ :=
  sourceAttachmentBit G i u * sourceAttachmentBit G i w

def targetAttachmentProduct {V : Type*}
    (H : SimpleGraph V) (i : V) (π : Equiv.Perm V) (u w : V) : ℕ :=
  targetAttachmentBit H i π u * targetAttachmentBit H i π w

/-- The exact deletion identity for a surviving distinct pair. -/
def deletionIdentity {V : Type*} [Fintype V]
    (G H : SimpleGraph V) (i : V) (π : Equiv.Perm V) (u w : V) : Prop :=
  (commonNeighborCount G u w : ℤ) -
      (sourceAttachmentProduct G i u w : ℤ) =
    (commonNeighborCount H (π u) (π w) : ℤ) -
      (targetAttachmentProduct H i π u w : ℤ)

/-- The unit-transfer conclusion from the deletion identity: the count
    difference is exactly b_u b_w-a_u a_w and lies in {-1,0,1}. -/
def unitTransferBound {V : Type*} [Fintype V]
    (G H : SimpleGraph V) (i : V) (π : Equiv.Perm V) (u w : V) : Prop :=
  ((commonNeighborCount H (π u) (π w) : ℤ) -
      (commonNeighborCount G u w : ℤ) =
    (targetAttachmentProduct H i π u w : ℤ) -
      (sourceAttachmentProduct G i u w : ℤ)) ∧
  ((commonNeighborCount H (π u) (π w) : ℤ) -
      (commonNeighborCount G u w : ℤ)) ∈ ({(-1 : ℤ), 0, 1} : Set ℤ)

/-- The graph isomorphism condition for a specified extension permutation. -/
def graphIsoMap {V : Type*}
    (G H : SimpleGraph V) (π : Equiv.Perm V) : Prop :=
  ∀ x y : V, G.Adj x y ↔ H.Adj (π x) (π y)

/-- The source attachment set S={u:a_u=1}, in the surviving source labels. -/
noncomputable def sourceAttachmentSet {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (i : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun u => sourceAttachmentBit G i u = 1)

/-- The target attachment set T={u:b_u=1}, indexed by the same surviving
    source labels as S. -/
noncomputable def targetAttachmentSet {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (i : V) (π : Equiv.Perm V) : Finset V := by
  classical
  exact Finset.univ.filter (fun u => targetAttachmentBit H i π u = 1)

/-- Claim 50738.  With the exact card-isomorphism carriers, the
    deck-determined common-neighbour value set, the deletion identity, and the
    {-1,0,1} unit-transfer bound all present, the no-consecutive hypothesis
    forces equality of the two counts and hence of the two attachment
    products. -/
def claim50738 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (i : V) (π : Equiv.Perm V),
    offVertexCardIso G H i π →
    commonNeighborValueSet G = commonNeighborValueSet H →
    noConsecutiveValues (commonNeighborValueSet G) →
    ∀ u w : V, u ≠ i → w ≠ i → u ≠ w →
      deletionIdentity G H i π u w →
      unitTransferBound G H i π u w →
      commonNeighborCount G u w = commonNeighborCount H (π u) (π w) ∧
        sourceAttachmentProduct G i u w =
          targetAttachmentProduct H i π u w

/-- Claim 50741.  Equal degree is expressed as equality of the two explicitly
    defined attachment-set cardinalities; equality of every surviving
    two-element product then identifies the sets, and the card isomorphism
    extends to the specified whole-graph isomorphism. -/
def claim50741 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (i : V) (π : Equiv.Perm V),
    offVertexCardIso G H i π →
    2 ≤ (sourceAttachmentSet G i).card →
    (sourceAttachmentSet G i).card =
      (targetAttachmentSet H i π).card →
    (∀ u w : V, u ≠ i → w ≠ i → u ≠ w →
      sourceAttachmentProduct G i u w =
        targetAttachmentProduct H i π u w) →
    sourceAttachmentSet G i = targetAttachmentSet H i π ∧
      graphIsoMap G H π

end

end MathlibPlus.Open.GraphTheory.R3458Claims50738_50741
