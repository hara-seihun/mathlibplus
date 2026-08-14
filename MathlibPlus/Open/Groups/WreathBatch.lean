import Mathlib

noncomputable section
namespace MathlibPlus.Open.Groups.Wreath

private def blockPartition {n m : ℕ} (B : Fin n → Finset (Fin (n * m))) : Prop :=
  (∀ i, (B i).card = m) ∧ ∀ x : Fin (n * m), ∃! i, x ∈ B i

private def intersectionMatrix {n m : ℕ} (B : Fin n → Finset (Fin (n * m)))
    (f : Fin (n * m) ≃ Fin (n * m)) : Matrix (Fin n) (Fin n) ℕ :=
  fun i j => (B i ∩ (B j).image f).card

private def blockPreserving {n m : ℕ} (B : Fin n → Finset (Fin (n * m)))
    (u : Fin (n * m) ≃ Fin (n * m)) : Prop :=
  ∃ σ : Fin n ≃ Fin n, ∀ i, (B i).image u = B (σ i)

private def sameBlockDoubleCoset {n m : ℕ} (B : Fin n → Finset (Fin (n * m)))
    (f g : Fin (n * m) ≃ Fin (n * m)) : Prop :=
  ∃ u v : Fin (n * m) ≃ Fin (n * m),
    blockPreserving B u ∧ blockPreserving B v ∧ g = u.trans (f.trans v)

/-- Block-intersection matrices classify wreath-product double cosets up to row and column permutations. -/
def blockIntersectionMatricesClassifyWreathDoubleCosets : Prop :=
  ∀ n m : ℕ, ∀ B : Fin n → Finset (Fin (n * m)), blockPartition B →
    ∀ f g : Fin (n * m) ≃ Fin (n * m),
      ((∃ α β : Fin n ≃ Fin n, ∀ i j,
          intersectionMatrix B f i j = intersectionMatrix B g (α i) (β j)) ↔
        sameBlockDoubleCoset B f g)

end MathlibPlus.Open.Groups.Wreath
