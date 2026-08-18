import MathlibPlus.Open.GraphTheory.Claim16172CayleyFiber

namespace MathlibPlus.Open.GraphTheory

/-- A connection set occurring in the ordinary Cayley-representation fiber of
`Cay(G,S)`, using the marked regular-pair presentation carrier. -/
def cayleyFiberMember16174 {G : Type*} [Fintype G] [Group G]
    (S T : Set G) : Prop :=
  ∃ (Ω : Type) (_ : Finite Ω) (Γ : SimpleGraph Ω) (o : Ω)
    (P Q : Subgroup (Equiv.Perm Ω))
    (mP : G ≃* P) (mQ : G ≃* Q),
    ordinaryCayleyPresentation16172 S Γ o P Q mP mQ ∧
      markedConnectionSet16172 Γ o mQ = T

/-- The carrier of the Cayley-representation fiber before quotienting by
`Aut(G)`. -/
def cayleyFiberType16174 {G : Type*} [Fintype G] [Group G]
    (S : Set G) :=
  {T : Set G // cayleyFiberMember16174 S T}

/-- The `Aut(G)` marking relation on the fiber carrier. -/
def cayleyFiberAutRelation16174 {G : Type*} [Fintype G] [Group G]
    (S : Set G) (T U : cayleyFiberType16174 S) : Prop :=
  ∃ α : G ≃* G, α '' T.1 = U.1

/-- A regular subgroup of the full graph automorphism group, isomorphic to
`G`.  The displayed member condition is the full-automorphism restriction. -/
def fullGraphRegularGSubgroup16174
    {G : Type*} [Fintype G] [Group G]
    (S : Set G) (P : Subgroup (Equiv.Perm G)) : Prop :=
  regularPermutationGroup16172 P ∧
    Nonempty (G ≃* P) ∧
      ∀ p : P,
        graphAutomorphism16172 (ordinaryCayleyGraph16172 S) p.1

/-- The carrier of regular copies of `G` in the full graph automorphism group. -/
def fullGraphRegularGSubgroupType16174
    {G : Type*} [Fintype G] [Group G]
    (S : Set G) :=
  {P : Subgroup (Equiv.Perm G) // fullGraphRegularGSubgroup16174 S P}

/-- Conjugacy inside the full graph automorphism group. -/
def fullGraphConjugacyRelation16174
    {G : Type*} [Fintype G] [Group G]
    (S : Set G)
    (P Q : fullGraphRegularGSubgroupType16174 S) : Prop :=
  ∃ a : Equiv.Perm G,
    graphAutomorphism16172 (ordinaryCayleyGraph16172 S) a ∧
      ∀ x : Equiv.Perm G,
        x ∈ Q.1 ↔
          ∃ y : Equiv.Perm G, y ∈ P.1 ∧ x = a * y * a⁻¹

/-- The exact fiber-multiplicity equality: the Cayley-representation fiber
and the conjugacy classes of regular `G`-subgroups of the full graph
automorphism group have the same cardinality. -/
def cayley_fiber_multiplicity_regular_subgroups : Prop :=
  ∀ (G : Type*) [Fintype G] [Group G] (S : Set G),
    S ⊆ ({1} : Set G)ᶜ →
      (∀ g : G, g ∈ S ↔ g⁻¹ ∈ S) →
        Nat.card (Quot (cayleyFiberAutRelation16174 S)) =
          Nat.card (Quot (fullGraphConjugacyRelation16174 S))

end MathlibPlus.Open.GraphTheory
