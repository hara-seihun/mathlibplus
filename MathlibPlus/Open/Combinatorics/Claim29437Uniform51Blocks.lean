import Mathlib

namespace MathlibPlus.Open.Combinatorics

/-- Claim 29437: every complement-normalized zero-mismatch type
`2^21 1^1` fixed-root involution in the order-43 `(5,5)`-good setting has
at least 51 balanced blocks whose two pairs have the same root adjacency. -/
def uniformFiftyOneSameRootBalancedBlocks_claim29437 : Prop :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  ∀ (G : SimpleGraph (Fin 43))
    (σ : Equiv.Perm (Fin 43))
    (r : Fin 43)
    (u v : Fin 21 → Fin 43),
    (∀ x, σ (σ x) = x) →
    (∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) →
    σ r = r →
    (∀ i : Fin 21,
      u i ≠ v i ∧ u i ≠ r ∧ v i ≠ r ∧
        σ (u i) = v i ∧ σ (v i) = u i) →
    Function.Injective u →
    Function.Injective v →
    (∀ i j : Fin 21, u i ≠ v j) →
    (∀ x : Fin 43, x = r ∨ ∃ i : Fin 21, x = u i ∨ x = v i) →
    (G.CliqueFree 5 ∧ G.IndepSetFree 5) →
    (∀ i : Fin 21, G.Adj (r) (u i) ↔ G.Adj r (v i)) →
    (∀ i : Fin 21, G.Adj (u i) (v i) ↔ G.Adj r (u i)) →
    let rootNeighbor : Fin 21 → Prop := fun i => G.Adj r (u i)
    let balanced : Fin 21 → Fin 21 → Prop := fun i j =>
      G.Adj (u i) (u j) ≠ G.Adj (u i) (v j)
    let sameRootBalancedCount : ℕ :=
      (Finset.univ.filter (fun p : Fin 21 × Fin 21 =>
        p.1.val < p.2.val ∧
          (rootNeighbor p.1 ↔ rootNeighbor p.2) ∧
          balanced p.1 p.2)).card
    ((
        (Finset.univ.filter rootNeighbor).card = 9 ∧
          (Finset.univ.filter (fun i : Fin 21 => ¬ rootNeighbor i)).card = 12) ∨
      (
        (Finset.univ.filter rootNeighbor).card = 10 ∧
          (Finset.univ.filter (fun i : Fin 21 => ¬ rootNeighbor i)).card = 11)) →
      51 ≤ sameRootBalancedCount

end MathlibPlus.Open.Combinatorics
