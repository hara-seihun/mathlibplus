import Mathlib

namespace MathlibPlus.Open.FormalizationBatch

/-- Claim 53857: support joins and the one/two-support consequences. -/
def supportJoinInjection : Prop :=
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
      ∀ P ∈ F,
        let Q := S P
        let DQ := F.filter (fun A => (S A ∩ Q) = ∅)
        let UQ := F.filter (fun B => Q ⊆ S B)
        ((∀ A ∈ DQ, A ∪ P ∈ UQ) ∧
          (∀ A ∈ DQ, ∀ B ∈ DQ, A ∪ P = B ∪ P → A = B) ∧
          DQ.card ≤ UQ.card) ∧
        (Q.card = 1 →
          ∃ i ∈ Q, ∃ b, b ∈ C i ∧ (∀ r ∈ C i, b ⊆ r) ∧
            2 * (F.filter (fun A => b ∈ Φ A)).card ≥ F.card) ∧
        (Q.card = 2 →
          ∃ i ∈ Q, ∃ j ∈ Q, i ≠ j ∧
            (∃ bᵢ, bᵢ ∈ C i ∧ (∀ r ∈ C i, bᵢ ⊆ r)) ∧
            (∃ bⱼ, bⱼ ∈ C j ∧ (∀ r ∈ C j, bⱼ ⊆ r)) ∧
            let n₀₀ := (F.filter (fun A => (S A ∩ Q).card = 0)).card
            let n₁₀ :=
              (F.filter (fun A => i ∈ S A ∧ j ∉ S A)).card
            let n₀₁ :=
              (F.filter (fun A => i ∉ S A ∧ j ∈ S A)).card
            let n₁₁ :=
              (F.filter (fun A => i ∈ S A ∧ j ∈ S A)).card
            let eᵢ := (F.filter (fun A => i ∈ S A)).card
            let eⱼ := (F.filter (fun A => j ∈ S A)).card
            n₀₀ + n₁₀ + n₀₁ + n₁₁ = F.card ∧
              n₀₀ ≤ n₁₁ ∧
              (eᵢ : ℤ) + (eⱼ : ℤ) - (F.card : ℤ) =
                (n₁₁ : ℤ) - (n₀₀ : ℤ) ∧
              (∃ bᵢ, bᵢ ∈ C i ∧ (∀ r ∈ C i, bᵢ ⊆ r) ∧
                2 * (F.filter (fun A => bᵢ ∈ Φ A)).card ≥ F.card) ∨
              (∃ bⱼ, bⱼ ∈ C j ∧ (∀ r ∈ C j, bⱼ ⊆ r) ∧
                2 * (F.filter (fun A => bⱼ ∈ Φ A)).card ≥ F.card)) ∧
        ((∀ x ∈ X, 2 * (F.filter (fun A => x ∈ A)).card < F.card) →
          ∀ σ : ℕ,
            ((∃ A ∈ F, (S A).Nonempty ∧ (S A).card = σ) ∧
              (∀ A ∈ F, (S A).Nonempty → σ ≤ (S A).card)) →
              3 ≤ σ)

end MathlibPlus.Open.FormalizationBatch
