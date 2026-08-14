import Mathlib

namespace MathlibPlus.Open.CayleyCI

private def inverseClosedConnectionSet {G : Type*} [AddGroup G] (S : Set G) : Prop :=
  (∀ x, x ∈ S → x ≠ 0) ∧ ∀ x, x ∈ S → -x ∈ S

private def cayleyAdjacency {G : Type*} [AddGroup G] (S : Set G) (x y : G) : Prop :=
  x ≠ y ∧ -x + y ∈ S

private def cayleyGraphIsomorphism {G : Type*} [AddGroup G]
    (S T : Set G) (e : G ≃ G) : Prop :=
  ∀ x y, cayleyAdjacency S x y ↔ cayleyAdjacency T (e x) (e y)

/-- A finite group is ordinary undirected CI when inverse-closed connection sets
are carried across Cayley-graph isomorphisms by group automorphisms. -/
def ordinaryUndirectedCI (G : Type*) [Fintype G] [AddGroup G] : Prop :=
  ∀ S T : Set G,
    inverseClosedConnectionSet S →
    inverseClosedConnectionSet T →
    (∃ e : G ≃ G, cayleyGraphIsomorphism S T e) →
    ∃ α : G ≃+ G, α '' S = T

/-- A negative witness for ordinary undirected CI keeps both connection sets
inverse-closed, as required for undirected Cayley graphs. -/
def ordinaryUndirectedCIWitness (G : Type*) [Fintype G] [AddGroup G] : Prop :=
  ∃ S T : Set G,
    inverseClosedConnectionSet S ∧
    inverseClosedConnectionSet T ∧
    (∃ e : G ≃ G, cayleyGraphIsomorphism S T e) ∧
    (∀ α : G ≃+ G, α '' S ≠ T)

private def connectedCayley {G : Type*} [AddGroup G] (S : Set G) : Prop :=
  AddSubgroup.closure S = ⊤

private def connectedInverseClosedCayleyDefect
    (G : Type*) [Fintype G] [AddGroup G] : Prop :=
  ∃ S T : Set G,
    inverseClosedConnectionSet S ∧
    inverseClosedConnectionSet T ∧
    connectedCayley S ∧
    connectedCayley T ∧
    (∃ e : G ≃ G, cayleyGraphIsomorphism S T e) ∧
    (∀ α : G ≃+ G, α '' S ≠ T)

private abbrev elementaryAbelian (p r : ℕ) := Fin r → ZMod p

/-- There is a connected inverse-closed Cayley-graph defect on `C₅⁸`. -/
def c5EightConnectedCayleyDefect : Prop :=
  connectedInverseClosedCayleyDefect (elementaryAbelian 5 8)

/-- There is a connected inverse-closed Cayley-graph defect on `C₇⁹`. -/
def c7NineConnectedCayleyDefect : Prop :=
  connectedInverseClosedCayleyDefect (elementaryAbelian 7 9)

/-- The settled low-prime negative ranges in the target interval. -/
def lowPrimeSettledNegativeRanges : Prop :=
  (∀ r : ℕ, 8 ≤ r → r ≤ 12 →
    ¬ ordinaryUndirectedCI (elementaryAbelian 5 r)) ∧
  (∀ r : ℕ, 9 ≤ r → r ≤ 16 →
    ¬ ordinaryUndirectedCI (elementaryAbelian 7 r))

end MathlibPlus.Open.CayleyCI
