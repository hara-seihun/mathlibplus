import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch.Laplacian

/-- Claim 44881: the complete marked Laplacian principal spectrum has graph-isomorphism fibres. -/
def claim44881 : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ∀ (G H : SimpleGraph (Fin n)),
      let edge : SimpleGraph (Fin n) → Fin n → Fin n → ℚ := fun K i j =>
        letI : Decidable (K.Adj i j) := Classical.propDecidable _
        if K.Adj i j then 1 else 0
      let degree : SimpleGraph (Fin n) → Fin n → ℚ := fun K i =>
        (@Fintype.card {v : Fin n // K.Adj i v} (Fintype.ofFinite _) : ℚ)
      let lap : SimpleGraph (Fin n) → Matrix (Fin n) (Fin n) ℚ := fun K i j =>
        if i = j then degree K i else -edge K i j
      (∃ σ : Equiv.Perm (Fin n),
        ∀ (S : Finset (Fin n)), S.Nonempty →
          Matrix.charpoly
              (fun i j : {x // x ∈ S} => lap G i.1 j.1) =
            Matrix.charpoly
              (fun i j : {x // x ∈ S.image σ} => lap H i.1 j.1)) ↔
        ∃ σ : Equiv.Perm (Fin n), ∀ i j : Fin n,
          G.Adj i j ↔ H.Adj (σ i) (σ j)

/-- Claim 44882: singleton and two-vertex Laplacian marks recover the graph. -/
def claim44882 : Prop :=
  ∀ (n : ℕ),
    ∀ (G : SimpleGraph (Fin n)),
      let edge : SimpleGraph (Fin n) → Fin n → Fin n → ℚ := fun K i j =>
        letI : Decidable (K.Adj i j) := Classical.propDecidable _
        if K.Adj i j then 1 else 0
      let degree : SimpleGraph (Fin n) → Fin n → ℚ := fun K i =>
        (@Fintype.card {v : Fin n // K.Adj i v} (Fintype.ofFinite _) : ℚ)
      let lap : SimpleGraph (Fin n) → Matrix (Fin n) (Fin n) ℚ := fun K i j =>
        if i = j then degree K i else -edge K i j
      let singleton : SimpleGraph (Fin n) → Fin n → Polynomial ℚ := fun K i =>
        Matrix.charpoly
          (fun a b : {x // x ∈ ({i} : Finset (Fin n))} => lap K a.1 b.1)
      let pair : SimpleGraph (Fin n) → Fin n → Fin n → Polynomial ℚ := fun K i j =>
        Matrix.charpoly
          (fun a b : {x // x ∈ ({i, j} : Finset (Fin n))} => lap K a.1 b.1)
      (∀ (K : SimpleGraph (Fin n)) (i : Fin n),
        -(singleton K i).constantCoeff = degree K i) ∧
      (∀ (K : SimpleGraph (Fin n)) (i j : Fin n), i ≠ j →
        (pair K i j).constantCoeff = degree K i * degree K j - edge K i j) ∧
      (∀ (H : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n)),
        ((∀ i : Fin n, singleton G i = singleton H (σ i)) ∧
          (∀ i j : Fin n, i ≠ j →
            (pair G i j).constantCoeff = (pair H (σ i) (σ j)).constantCoeff)) →
        ∀ i j : Fin n, G.Adj i j ↔ H.Adj (σ i) (σ j))

end MathlibPlus.Open.ResearchFormalizationBatch.Laplacian
