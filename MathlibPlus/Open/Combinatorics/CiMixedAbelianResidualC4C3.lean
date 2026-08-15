import Mathlib

namespace MathlibPlus.Open.CiMixedAbelianResidualC4C3

/-- Inverse-closed subsets of an additive group. -/
def inverseClosed {A : Type*} [Neg A] (S : Set A) : Prop :=
  ∀ ⦃x : A⦄, x ∈ S → -x ∈ S

/-- Subsets that do not contain the additive identity. -/
def identityFree {A : Type*} [Zero A] (S : Set A) : Prop :=
  0 ∉ S

/-- The ordinary undirected Cayley graph of an additive group. -/
def cayleyGraph {A : Type*} [AddGroup A] (S : Set A) : SimpleGraph A :=
  SimpleGraph.fromRel (fun x y => y - x ∈ S)

/-- Closed neighborhoods in a simple graph. -/
def closedNeighborhood {X : Type*} (graph : SimpleGraph X) (x : X) : Set X :=
  {y | y = x ∨ graph.Adj x y}

/-- Distinct vertices have distinct closed neighborhoods. -/
def trueTwinFree {X : Type*} (graph : SimpleGraph X) : Prop :=
  ∀ ⦃x y : X⦄, x ≠ y → closedNeighborhood graph x ≠ closedNeighborhood graph y

/-- Isomorphism of two simple graphs. -/
def graphIsomorphism {X Y : Type*}
    (leftGraph : SimpleGraph X) (rightGraph : SimpleGraph Y) : Prop :=
  ∃ e : X ≃ Y, ∀ x y, leftGraph.Adj x y ↔ rightGraph.Adj (e x) (e y)

abbrev K : Type := ZMod 4
abbrev V : Type := Fin 3 → ZMod 3
abbrev G : Type := K × V

/-- The connection set displayed in the claim. -/
def sU (U : Set V) : Set G :=
  (((Set.univ : Set K) \ {0}) ×ˢ ({0} : Set V)) ∪
    ((Set.univ : Set K) ×ˢ U)

/-- Exact admitted claim 60080. -/
def claim60080 : Prop :=
  ∀ (U : Set V),
    inverseClosed U →
    U ⊆ {v : V | v ≠ 0} →
    trueTwinFree (cayleyGraph U) →
    ∀ (T : Set G),
      inverseClosed T →
      identityFree T →
      graphIsomorphism (cayleyGraph (sU U)) (cayleyGraph T) →
      ∃ α : G ≃+ G, α '' sU U = T

end MathlibPlus.Open.CiMixedAbelianResidualC4C3
