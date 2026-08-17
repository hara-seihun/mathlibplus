import Mathlib

namespace MathlibPlus.Open.FormalizationBatch

/-- Claim 53859: the exact necessary signature in the seven/eight-chain
    residual class. -/
def sevenEightChainResidualSignature53859 : Prop :=
  ∀ {α : Type} [DecidableEq α]
    (F : Finset (Finset α)) (X : Finset α),
    (∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F) →
    X = F.biUnion (fun A : Finset α => A) →
    (∀ x ∈ X, ∃ A ∈ F, x ∉ A) →
    ∀ (t : ℕ) (C : Fin t → Finset (Finset α)),
      (∀ i, (C i).Nonempty) →
      (∀ i r s, r ∈ C i → s ∈ C i → r ⊆ s ∨ s ⊆ r) →
      (∀ i r, r ∈ C i → r ∈ X.biUnion (fun x =>
        {(F.filter (fun A => x ∉ A)).biUnion (fun A : Finset α => A)})) →
      (∀ r, r ∈ X.biUnion (fun x =>
        {(F.filter (fun A => x ∉ A)).biUnion (fun A : Finset α => A)}) →
        ∃! i, r ∈ C i) →
      let root : α → Finset α := fun x =>
        (F.filter (fun A => x ∉ A)).biUnion (fun A : Finset α => A)
      let R : Finset (Finset α) := X.biUnion (fun x => {root x})
      let Φ : Finset α → Finset (Finset α) := fun A =>
        R.filter (fun r => ¬ A ⊆ r)
      let S : Finset α → Finset (Fin t) := fun A =>
        Finset.univ.filter (fun i => (Φ A ∩ C i).Nonempty)
      ∀ σ : ℕ,
        (∀ x ∈ X, 2 * (F.filter (fun A => x ∈ A)).card < F.card) →
        ((∃ A ∈ F, (S A).Nonempty ∧ (S A).card = σ) ∧
          (∀ A ∈ F, (S A).Nonempty → σ ≤ (S A).card)) →
        (t = 7 ∨ t = 8) →
        σ = 3 ∧
        ∃ P ∈ F, (S P).card = 3 ∧
          let Q := S P
          let N₀ := (F.filter (fun A => (S A ∩ Q).card = 0)).card
          let N₁ := (F.filter (fun A => (S A ∩ Q).card = 1)).card
          let N₂ := (F.filter (fun A => (S A ∩ Q).card = 2)).card
          let N₃ := (F.filter (fun A => (S A ∩ Q).card = 3)).card
          N₀ ≤ N₃ ∧
            (N₁ : ℚ) + 2 * (N₂ : ℚ) + 3 * (N₃ : ℚ) <
              3 * (F.card : ℚ) / 2 ∧
            N₂ + 3 * (N₃ - N₀) < N₁ ∧
            N₂ ≤ N₂ + 3 * (N₃ - N₀) ∧
            N₂ ≤ N₁

end MathlibPlus.Open.FormalizationBatch
