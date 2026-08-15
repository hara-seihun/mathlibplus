import Mathlib

namespace MathlibPlus.Open.CI

/-- A connection set is inverse-closed in additive notation. -/
def inverseClosedConnectionSet {G : Type*} [Neg G] (S : Set G) : Prop :=
  ∀ x, x ∈ S ↔ -x ∈ S

/-- The connection-set complement is taken inside the nonzero elements. -/
def complementaryConnectionSet {G : Type*} [Zero G] (S : Set G) : Set G :=
  {x | x ≠ 0 ∧ x ∉ S}

/-- The ordinary undirected Cayley graph associated to an additive connection set. -/
def additiveCayleyGraph {G : Type*} [AddGroup G] (S : Set G) : SimpleGraph G :=
  SimpleGraph.fromRel (fun x y => y - x ∈ S)

/-- The usual CI property for an ordinary undirected Cayley graph. -/
def ordinaryUndirectedCI {G : Type*} [AddCommGroup G] (S : Set G) : Prop :=
  S ⊆ ({0} : Set G)ᶜ ∧
    inverseClosedConnectionSet S ∧
      ∀ T : Set G,
        T ⊆ ({0} : Set G)ᶜ →
        inverseClosedConnectionSet T →
          ∀ _graphIso : additiveCayleyGraph S ≃g additiveCayleyGraph T,
            ∃ groupAut : G ≃+ G, ∀ x, x ∈ S ↔ groupAut x ∈ T

/--
For every positive rank `r`, the Cayley graph on `C_2^r × C_9` has the CI
property at minimum valency `r + 1`, and also when that minimum valency is
attained by the complementary connection set.
-/
def c2PowC9ConnectedMinimumValencyCI : Prop :=
  ∀ r : ℕ, 1 ≤ r →
    let G := (Fin r → ZMod 2) × ZMod 9
    ∀ S : Set G,
      S ⊆ ({0} : Set G)ᶜ →
      inverseClosedConnectionSet S →
      ((AddSubgroup.closure S = ⊤ ∧ S.ncard = r + 1) ∨
        (AddSubgroup.closure (complementaryConnectionSet S) = ⊤ ∧
          (complementaryConnectionSet S).ncard = r + 1)) →
      ordinaryUndirectedCI S

end MathlibPlus.Open.CI
