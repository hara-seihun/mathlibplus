import MathlibPlus.Open.NewResearch2.R0399MatchedProfiles

namespace MathlibPlus.Open.NewResearch2.R0399MatchedProfiles

noncomputable section

/-- In the exact finite-lattice carrier, incidence is the set of
join-irreducibles below an element and the tight cube coordinate is the join
of the outside coordinate with the finite join of a tight subset. -/
def claim20929 : Prop :=
  ∀ {L : Type*} [Fintype L] [DecidableEq L] [Lattice L] [BoundedOrder L]
    (j : L) (T : Finset L),
    canonicalTightCube j T →
      (∀ x : L,
        incidence x = {u : L | joinIrreducible u ∧ u ≤ x}) ∧
        (∀ S : Finset L, S ⊆ T →
          cubeCoordinate j S = j ⊔ finiteJoin S)

end

end MathlibPlus.Open.NewResearch2.R0399MatchedProfiles
