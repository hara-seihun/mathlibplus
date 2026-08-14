import Mathlib

namespace MathlibPlus
namespace Open
namespace C3NextToMinimalConnectedValency

/-- The vector space `F_3^r`, represented as functions from `Fin r` to `ZMod 3`. -/
abbrev F3Vector (r : ℕ) := Fin r → ZMod 3

/-- The concrete adjacency relation of the Cayley graph with connection set `S`. -/
def cayleyAdjacency {r : ℕ} (S : Finset (F3Vector r))
    (x y : F3Vector r) : Prop :=
  x ≠ y ∧ y - x ∈ S

/-- Isomorphism of the concrete undirected Cayley graphs determined by `S` and `T`. -/
def cayleyGraphIsomorphic {r : ℕ} (S T : Finset (F3Vector r)) : Prop :=
  ∃ e : F3Vector r ≃ F3Vector r,
    ∀ x y, cayleyAdjacency S x y ↔ cayleyAdjacency T (e x) (e y)

/-- Connectivity of a Cayley graph, expressed by reachability in its adjacency relation. -/
def cayleyGraphConnected {r : ℕ} (S : Finset (F3Vector r)) : Prop :=
  ∀ x y : F3Vector r, Relation.ReflTransGen (cayleyAdjacency S) x y

/-- The CI property for a fixed connection set in `F_3^r`. -/
def c3CayleyCI (r : ℕ) (S : Finset (F3Vector r)) : Prop :=
  ∀ T : Finset (F3Vector r),
    (∀ v, v ∈ T → v ≠ 0) →
    (∀ v, v ∈ T → -v ∈ T) →
    cayleyGraphIsomorphic S T →
    ∃ A : F3Vector r ≃ₗ[ZMod 3] F3Vector r,
      ∀ v, v ∈ S ↔ A v ∈ T

/--
The admitted CI claim for inverse-closed spanning subsets of `F_3^r` of
valency `2r+2`, together with its stated rank-six and rank-seven instances.
-/
def c3NextToMinimalConnectedValencyCI : Prop :=
  (∀ (r : ℕ), 2 ≤ r →
    ∀ S : Finset (F3Vector r),
      (∀ v, v ∈ S → v ≠ 0) →
      (∀ v, v ∈ S → -v ∈ S) →
      Submodule.span (ZMod 3) (S : Set (F3Vector r)) = ⊤ →
      S.card = 2 * r + 2 →
      c3CayleyCI r S) ∧
  (∀ S : Finset (F3Vector 6),
    (∀ v, v ∈ S → v ≠ 0) →
    (∀ v, v ∈ S → -v ∈ S) →
    cayleyGraphConnected S →
    S.card = 14 →
    c3CayleyCI 6 S) ∧
  (∀ S : Finset (F3Vector 7),
    (∀ v, v ∈ S → v ≠ 0) →
    (∀ v, v ∈ S → -v ∈ S) →
    cayleyGraphConnected S →
    S.card = 16 →
    c3CayleyCI 7 S)

end C3NextToMinimalConnectedValency
end Open
end MathlibPlus
