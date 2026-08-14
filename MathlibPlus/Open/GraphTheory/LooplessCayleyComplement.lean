import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Inverse-closed, identity-free connection sets for ordinary undirected
Cayley graphs. -/
def inverseClosedFinset {G : Type*} [Group G] (S : Finset G) : Prop :=
  ∀ x : G, x ∈ S ↔ x⁻¹ ∈ S

/-- The loopless Cayley adjacency relation determined by a finite connection
set. -/
def cayleyAdjacency {G : Type*} [Group G] (S : Finset G) (x y : G) : Prop :=
  x ≠ y ∧ x⁻¹ * y ∈ S

/-- Exact graph isomorphism of the two Cayley adjacency relations. -/
def cayleyGraphIso {G : Type*} [Group G] (S T : Finset G) : Prop :=
  ∃ e : Equiv.Perm G, ∀ x y : G,
    cayleyAdjacency S x y ↔ cayleyAdjacency T (e x) (e y)

/-- Ordinary graph complementation removes the identity loop. -/
def looplessCayleyComplement {G : Type*} [Fintype G] [DecidableEq G]
    [Group G] (S : Finset G) : Finset G :=
  (Finset.univ.erase 1) \ S

/-- The CI property at one valency, with the graph-isomorphism fiber stated
against group automorphisms rather than an abstract callback. -/
def ordinaryCayleyCIAt {G : Type*} [Fintype G] [DecidableEq G]
    [Group G] (k : ℕ) : Prop :=
  ∀ S T : Finset G,
    1 ∉ S → 1 ∉ T →
    inverseClosedFinset S → inverseClosedFinset T →
    S.card = k → T.card = k →
    cayleyGraphIso S T →
    ∃ α : G ≃* G, α '' (S : Set G) = (T : Set G)

/-- Claim 43659: for every finite group of order 220, the loopless complement
has connection set `(G \ {1}) \ S`, valency `219-k`, and preserves exact
Cayley graph-isomorphism fibers and the CI property. -/
def complementTransferQ220 : Prop :=
  ∀ (G : Type*) [Fintype G] [DecidableEq G] [Group G],
    Fintype.card G = 220 →
    (∀ S : Finset G, 1 ∉ S →
      (looplessCayleyComplement S).card = 219 - S.card) ∧
    (∀ S T : Finset G,
      cayleyGraphIso S T ↔
        cayleyGraphIso (looplessCayleyComplement S)
          (looplessCayleyComplement T)) ∧
    (∀ k : ℕ, k ≤ 219 →
      ordinaryCayleyCIAt (G := G) k ↔ ordinaryCayleyCIAt (G := G) (219 - k))

end MathlibPlus.Open.GraphTheory
