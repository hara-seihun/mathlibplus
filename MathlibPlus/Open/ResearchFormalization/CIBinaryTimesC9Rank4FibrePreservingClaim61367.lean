import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.CIBinaryTimesC9Rank4FibrePreservingClaim61367

noncomputable section

abbrev BinaryVector4 := Fin 4 → ZMod 2
abbrev Group61367 := BinaryVector4 × ZMod 9
abbrev RankFourAutomorphism61367 :=
  (BinaryVector4 ≃ₗ[ZMod 2] BinaryVector4) ×
    (ZMod 9 ≃+ ZMod 9)

/-- The standard cyclic-nine fibre over a binary base point. -/
def standardC9Fiber61367 (x : BinaryVector4) : Set Group61367 :=
  {p | p.1 = x}

/-- A bijection preserves the standard partition into the sixteen cyclic-nine
fibres when it maps each displayed fibre onto a displayed fibre. -/
def preservesStandardC9Partition61367 (f : Group61367 ≃ Group61367) : Prop :=
  ∀ x : BinaryVector4, ∃ y : BinaryVector4,
    f '' standardC9Fiber61367 x = standardC9Fiber61367 y

/-- The ordinary additive Cayley adjacency relation on the exact rank-four
binary-times-cyclic-nine carrier. -/
def cayleyAdjacency61367
    (S : Set Group61367) (x y : Group61367) : Prop :=
  ∃ s ∈ S, y = x + s

/-- Graph isomorphism for the ordinary undirected Cayley graphs in the claim. -/
def cayleyGraphIsomorphism61367
    (S T : Set Group61367) (f : Group61367 ≃ Group61367) : Prop :=
  ∀ x y : Group61367,
    cayleyAdjacency61367 S x y ↔
      cayleyAdjacency61367 T (f x) (f y)

/-- Identity-free and inverse-closed connection sets on the displayed group. -/
def inverseClosedConnectionSet61367 (S : Set Group61367) : Prop :=
  S ⊆ (Set.univ \ ({0} : Set Group61367)) ∧
    ∀ x, x ∈ S → -x ∈ S

/-- The componentwise action of `GL(4,2) × Aut(C₉)` on the exact group. -/
def rankFourAutomorphismAction61367
    (α : RankFourAutomorphism61367) : Group61367 ≃+ Group61367 :=
  AddEquiv.prodCongr α.1.toAddEquiv α.2

/-- Claim 61367: every ordinary undirected Cayley-graph isomorphism on
`(F₂^4) × C₉` that preserves the standard sixteen C₉-fibres is induced on
its connection set by a componentwise group automorphism. -/
def claim61367 : Prop :=
  Fintype.card Group61367 = 144 ∧
    ∀ (S T : Set Group61367),
      inverseClosedConnectionSet61367 S →
        inverseClosedConnectionSet61367 T →
          ∀ f : Group61367 ≃ Group61367,
            preservesStandardC9Partition61367 f →
              cayleyGraphIsomorphism61367 S T f →
                ∃ α : RankFourAutomorphism61367,
                  rankFourAutomorphismAction61367 α '' S = T

end

end MathlibPlus.Open.ResearchFormalization.CIBinaryTimesC9Rank4FibrePreservingClaim61367
