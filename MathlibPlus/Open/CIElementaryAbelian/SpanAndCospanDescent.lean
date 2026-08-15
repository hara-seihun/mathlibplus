import Mathlib

namespace MathlibPlus.Open

namespace CIElementaryAbelian

/-- The elementary-abelian vector space `F_p^r`, represented as functions on `Fin r`. -/
abbrev V (p r : ℕ) := Fin r → ZMod p

/-- A connection set contains no identity element. -/
def identityFree {α : Type*} [Zero α] (S : Set α) : Prop :=
  (0 : α) ∉ S

/-- A connection set is closed under taking inverses. -/
def inverseClosed {α : Type*} [Neg α] (S : Set α) : Prop :=
  ∀ ⦃x : α⦄, x ∈ S → -x ∈ S

/-- Adjacency in the ordinary (simple, undirected) Cayley graph of an additive group. -/
def cayleyAdjacent {α : Type*} [AddGroup α] (S : Set α) (x y : α) : Prop :=
  x ≠ y ∧ x - y ∈ S

/-- An isomorphism of the ordinary Cayley graphs, written without introducing a graph API. -/
def cayleyGraphIso {α β : Type*} [AddGroup α] [AddGroup β]
    (S : Set α) (T : Set β) : Prop :=
  ∃ e : α ≃ β, ∀ x y, cayleyAdjacent S x y ↔ cayleyAdjacent T (e x) (e y)

/-- An ordinary undirected Cayley-graph defect over a common scalar ring. -/
def undirectedCayleyDefect {K α β : Type*}
    [Ring K] [AddCommGroup α] [AddCommGroup β]
    [Module K α] [Module K β]
    (S : Set α) (T : Set β) : Prop :=
  identityFree S ∧
    inverseClosed S ∧
    identityFree T ∧
    inverseClosed T ∧
    cayleyGraphIso S T ∧
    ¬ ∃ e : α ≃ₗ[K] β, e '' S = T

/-- Restriction of a connection set to a submodule containing its elements. -/
def restrictSet {K α : Type*} [Semiring K] [AddCommMonoid α] [Module K α]
    (W : Submodule K α) (S : Set α) : Set W :=
  {x | (x : α) ∈ S}

/-- The nonzero complement of a connection set. -/
def puncturedComplement {α : Type*} [Zero α] (S : Set α) : Set α :=
  Set.univ \ (S ∪ {0})

/--
The admitted span-and-co-span descent obstruction.  All graph isomorphisms are
arbitrary vertex bijections, while the forbidden equivalences are linear
isomorphisms, matching the distinction between Cayley-graph isomorphism and
`GL(V)` equivalence in the claim.
-/
def spanAndCospanDescentObstruction : Prop :=
  ∀ (p r : ℕ) (hp : p.Prime),
    5 ≤ p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ (S T : Set (V p r)),
        undirectedCayleyDefect (K := ZMod p) S T →
          let W : Submodule (ZMod p) (V p r) := Submodule.span (ZMod p) S
          let W' : Submodule (ZMod p) (V p r) := Submodule.span (ZMod p) T
          let SStar : Set (V p r) := puncturedComplement S
          let TStar : Set (V p r) := puncturedComplement T
          let U : Submodule (ZMod p) (V p r) := Submodule.span (ZMod p) SStar
          let U' : Submodule (ZMod p) (V p r) := Submodule.span (ZMod p) TStar
          Module.finrank (ZMod p) W = Module.finrank (ZMod p) W' ∧
            undirectedCayleyDefect (K := ZMod p) (restrictSet W S) (restrictSet W' T) ∧
            Module.finrank (ZMod p) U = Module.finrank (ZMod p) U' ∧
            undirectedCayleyDefect (K := ZMod p) (restrictSet U SStar) (restrictSet U' TStar) ∧
            ((6 ≤ r ∧ r ≤ 2 * p + 2) →
              6 ≤ Module.finrank (ZMod p) W ∧
                6 ≤ Module.finrank (ZMod p) U ∧
                12 ≤ S.ncard ∧
                S.ncard ≤ p ^ r - 13)

end CIElementaryAbelian

end MathlibPlus.Open
