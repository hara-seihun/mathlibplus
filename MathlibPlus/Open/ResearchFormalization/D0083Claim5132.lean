import MathlibPlus.Open.Combinatorics.TreeAttachment

namespace MathlibPlus.Open.ResearchFormalization.D0083

open MathlibPlus.Open.Combinatorics.TreeAttachment

noncomputable section

abbrev rootedOccurrenceSpace (n : ℕ) :=
  RootedCardSpace (n - 1)

abbrev treePresentationSpace (n : ℕ) :=
  TreeSpace n

/-- The occurrence basis vector indexed by a chosen unlabelled card and a
vertex of its canonical representative. -/
def rootedOccurrenceBasis (n : ℕ) (C : UnlabelledTree (n - 1))
    (v : Vertex (n - 1)) : rootedOccurrenceSpace n :=
  rootedBasis C v

/-- The basis vector indexed by an unlabelled target tree. -/
def treePresentationBasis (n : ℕ) (T : UnlabelledTree n) :
    treePresentationSpace n :=
  treeBasis T

/-- Claim 5132: the rooted-card occurrence space is the rational direct sum
of the vertex spaces of unlabelled `(n-1)`-tree cards, and the target space is
the rational space freely based by unlabelled `n`-trees. -/
def claim5132 : Prop :=
  ∀ n : ℕ,
    (∃ b : Module.Basis (RootedOccurrence (n - 1)) ℚ
        (rootedOccurrenceSpace n),
      ∀ (C : UnlabelledTree (n - 1)) (v : Vertex (n - 1)),
        b ⟨C, v⟩ = rootedOccurrenceBasis n C v) ∧
      (∃ b : Module.Basis (UnlabelledTree n) ℚ
          (treePresentationSpace n),
        ∀ T : UnlabelledTree n,
          b T = treePresentationBasis n T)

end
end MathlibPlus.Open.ResearchFormalization.D0083
