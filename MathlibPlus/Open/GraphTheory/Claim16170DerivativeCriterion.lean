import Mathlib
import MathlibPlus.Open.ResearchFormalization.R1022

namespace MathlibPlus.Open.GraphTheory

/-- A set is a union of the orbits of the normalized derivative group. -/
def derivativeGroup16170 {G : Type*} [Group G]
    (f : Equiv.Perm G) : Subgroup (Equiv.Perm G) :=
  Subgroup.closure
    (Set.range (MathlibPlus.Open.ResearchFormalization.R1022.relativeDerivative f))

def derivativeOrbitUnion16170 {G : Type*} [Group G]
    (f : Equiv.Perm G) (S : Set G) : Prop :=
  ∀ d : derivativeGroup16170 f,
    Set.image d.1 S = S

/-- The graph-isomorphism condition for the displayed permutation f. -/
def normalizedCayleyGraphIso16170 {G : Type*} [Group G]
    (S T : Set G) (f : Equiv.Perm G) : Prop :=
  ∀ x y : G,
    (SimpleGraph.mulCayley S).Adj x y ↔
      (SimpleGraph.mulCayley T).Adj (f x) (f y)

/-- Claim 16170: the normalized relative-derivative criterion for a Cayley
presentation. -/
def derivative_criterion : Prop :=
  ∀ (G : Type*) [Fintype G] [Group G] (S : Set G) (f : Equiv.Perm G),
    f (1 : G) = 1 →
      S ⊆ ({1} : Set G)ᶜ →
        (normalizedCayleyGraphIso16170 S (f '' S) f ↔
          derivativeOrbitUnion16170 f S)

end MathlibPlus.Open.GraphTheory
