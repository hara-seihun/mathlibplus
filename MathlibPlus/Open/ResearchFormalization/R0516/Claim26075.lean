import MathlibPlus.Open.Combinatorics.FixedSupportClaim26067

namespace MathlibPlus.Open.ResearchFormalization.R0516.Claim26075

noncomputable section

private def deletedComplement {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V) :
    SimpleGraph {v : V // v ∉ (S : Set V)} :=
  T.induce ((S : Set V)ᶜ)

private def supportGraph {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V) :
    SimpleGraph {v : V // v ∈ (S : Set V)} :=
  T.induce (S : Set V)

private def boundaryEdges {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V) : Set (V × V) :=
  {p |
    p.1 ∈ (S : Set V) ∧
      p.2 ∉ (S : Set V) ∧
        T.Adj p.1 p.2}

private def attachmentEdges {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V)
    (C : (deletedComplement T S).ConnectedComponent) : Set (V × V) :=
  {p |
    ∃ hs : p.1 ∈ (S : Set V),
      ∃ ho : p.2 ∉ (S : Set V),
        T.Adj p.1 p.2 ∧
          (deletedComplement T S).connectedComponentMk ⟨p.2, ho⟩ = C}

private def boundaryCount {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V) : ℕ :=
  Set.ncard (boundaryEdges T S)

private def attachmentCount {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V)
    (C : (deletedComplement T S).ConnectedComponent) : ℕ :=
  Set.ncard (attachmentEdges T S C)

private def deletedComponentCount {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V) : ℕ :=
  Nat.card (deletedComplement T S).ConnectedComponent

/-- Claim 26075: for a nonempty connected support in a finite tree, each
component of the induced deleted complement has exactly one oriented
boundary edge into the support, and the deleted-component count equals the
boundary-edge count. -/
def claim26075 : Prop :=
  ∀ {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V),
    T.IsTree →
      S.Nonempty →
        (supportGraph T S).Preconnected →
          (∀ C : (deletedComplement T S).ConnectedComponent,
            attachmentCount T S C = 1) ∧
            deletedComponentCount T S = boundaryCount T S

end

end MathlibPlus.Open.ResearchFormalization.R0516.Claim26075
