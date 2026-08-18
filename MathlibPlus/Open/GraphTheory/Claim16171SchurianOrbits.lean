import MathlibPlus.Open.GraphTheory.Claim16172CayleyFiber

namespace MathlibPlus.Open.GraphTheory

/-- The orbit of `x` under the normalized derivative group. -/
def derivativeOrbit16171 {G : Type*} [Group G]
    (f : Equiv.Perm G) (x : G) : Set G :=
  {y | ∃ d : derivativeGroup16172 f, d.1 x = y}

/-- Claim 16171: the normalized derivative orbits are the identity-stabilizer
orbits of `K_f = ⟨R(G), f⁻¹ R(G) f⟩`, and hence the Schurian basic sets of
`V(G,(K_f)_1)`. -/
def derivative_orbits_equal_schurian_basic_sets_claim16171 : Prop :=
  ∀ (G : Type*) [Fintype G] [Group G] (f : Equiv.Perm G),
    f (1 : G) = 1 →
      (∀ x : G,
        derivativeOrbit16171 f x = schurianBasicSet16172 f x) ∧
      (∀ S : Set G,
        derivativeOrbitUnion16172 f S ↔ isAfSubset16172 f S)

end MathlibPlus.Open.GraphTheory
