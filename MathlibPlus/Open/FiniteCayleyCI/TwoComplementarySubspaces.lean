import Mathlib

namespace MathlibPlus.Open.FiniteCayleyCI

/-- A connection set does not contain the identity. -/
def IdentityFree {G : Type*} [Zero G] (S : Set G) : Prop :=
  0 ∉ S

/-- A connection set is closed under taking inverses. -/
def InverseClosed {G : Type*} [Neg G] (S : Set G) : Prop :=
  ∀ ⦃x : G⦄, x ∈ S → -x ∈ S

/-- Two subspaces form an internal direct sum spanning the ambient space. -/
def ComplementarySubspaces {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (U W : Submodule K V) : Prop :=
  U ⊔ W = ⊤ ∧ Disjoint U W

/-- Isomorphism of the ordinary undirected Cayley graphs represented by their
    difference-adjacency relations. -/
def OrdinaryCayleyGraphIso {V : Type*} [AddCommGroup V]
    (S T : Set V) : Prop :=
  ∃ e : V → V, Function.Bijective e ∧
    ∀ x y : V, (y - x ∈ S ↔ e y - e x ∈ T)

/-- Two complementary nonzero subspaces over an odd prime field give a CI
    connection set for ordinary undirected Cayley graphs. -/
def twoComplementarySubspacesCI (p : ℕ) [Fact p.Prime] : Prop :=
  Odd p →
    ∀ (V : Type*) [AddCommGroup V] [Module (ZMod p) V]
      [FiniteDimensional (ZMod p) V]
      (U W : Submodule (ZMod p) V),
      U ≠ ⊥ →
      W ≠ ⊥ →
      ComplementarySubspaces U W →
      let S : Set V := ((U : Set V) \ {0}) ∪ ((W : Set V) \ {0})
      IdentityFree S ∧
        InverseClosed S ∧
          ∀ T : Set V,
            IdentityFree T →
            InverseClosed T →
            OrdinaryCayleyGraphIso S T →
            ∃ L : V ≃ₗ[ZMod p] V, L '' T = S

end MathlibPlus.Open.FiniteCayleyCI
