import Mathlib

namespace MathlibPlus.Open.Research

/-- The point action of a permutation preserves the adjacency relation of a graph. -/
def graph_automorphism (Γ : SimpleGraph (Fin 90)) (f : Equiv.Perm (Fin 90)) : Prop :=
  ∀ x y, Γ.Adj (f x) (f y) ↔ Γ.Adj x y

/-- An explicit finite block-system formulation of the block data in Claim 39517. -/
def common_invariant_block_system
    (Γ : SimpleGraph (Fin 90)) (b d : Nat)
    (blocks : Fin d → Finset (Fin 90)) : Prop :=
  d = 90 / b ∧
    (∀ i, (blocks i).card = b) ∧
    (∀ x, ∃ i, x ∈ blocks i) ∧
    (∀ ⦃i j⦄, i ≠ j → Disjoint (blocks i) (blocks j)) ∧
    (∀ f : Equiv.Perm (Fin 90), graph_automorphism Γ f →
      ∃ q : Equiv.Perm (Fin d),
        ∀ i, Finset.image f (blocks i) = blocks (q i))

def block_adjacency
    (Γ : SimpleGraph (Fin 90))
    (blocks : Fin d → Finset (Fin 90))
    (ι : ∀ i : Fin d, (Fin b) ≃ {x // x ∈ blocks i})
    (i j : Fin d) (u v : Fin b) : Prop :=
  Γ.Adj (ι i u) (ι j v)

/-- The fiber-family relation called `Lift_Γ(q)` in Claim 39517. -/
def graph_lift
    (Γ : SimpleGraph (Fin 90)) (b d : Nat)
    (blocks : Fin d → Finset (Fin 90))
    (ι : ∀ i : Fin d, (Fin b) ≃ {x // x ∈ blocks i})
    (q : Equiv.Perm (Fin d)) :
    Set (∀ i : Fin d, Fin b → Fin b) :=
  {φ | ∀ (i j : Fin d) (u v : Fin b),
      block_adjacency Γ blocks ι (q i) (q j) (φ i u) (φ j v) ↔
        block_adjacency Γ blocks ι i j u v}

/-- The induced permutation of the block quotient, written without an opaque
callback for `ρ(Aut Γ)`. -/
def induced_block_image
    (Γ : SimpleGraph (Fin 90)) (b d : Nat)
    (blocks : Fin d → Finset (Fin 90))
    (q : Equiv.Perm (Fin d)) : Prop :=
  ∃ f : Equiv.Perm (Fin 90),
    graph_automorphism Γ f ∧
      ∀ i, Finset.image f (blocks i) = blocks (q i)

/-- Claim 39517: the graph-dependent quotient lift is exact. -/
def graph_dependent_quotient_lift : Prop :=
  ∀ (Γ : SimpleGraph (Fin 90)) (b d : Nat)
    (blocks : Fin d → Finset (Fin 90)),
    common_invariant_block_system Γ b d blocks →
    (∀ ι : ∀ i : Fin d, (Fin b) ≃ {x // x ∈ blocks i},
      ∀ q : Equiv.Perm (Fin d),
        induced_block_image Γ b d blocks q ↔
          (graph_lift Γ b d blocks ι q).Nonempty)

end MathlibPlus.Open.Research
