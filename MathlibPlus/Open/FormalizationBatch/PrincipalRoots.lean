import Mathlib

namespace MathlibPlus.Open.FormalizationBatch

/-- Claim 53856: principal-root compression for a finite union-closed family. -/
def principalRootCompression : Prop :=
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
      let R : Finset (Finset α) :=
        X.biUnion (fun x => {root x})
      let Φ : Finset α → Finset (Finset α) := fun A =>
        R.filter (fun r => ¬ A ⊆ r)
      let S : Finset α → Finset (Fin t) := fun A =>
        Finset.univ.filter (fun i => (Φ A ∩ C i).Nonempty)
      (∀ A ∈ F, ∀ B ∈ F, Φ (A ∪ B) = Φ A ∪ Φ B) ∧
      (∀ A ∈ F, ∀ B ∈ F, Φ A = Φ B → A = B) ∧
      (∀ A ∈ F, ∀ x ∈ X, (root x ∉ Φ A ↔ x ∉ A)) ∧
      (∀ x ∈ X,
        (F.filter (fun A => root x ∈ Φ A)).card =
          (F.filter (fun A => x ∈ A)).card) ∧
      (∀ A ∈ F, ∀ i r s,
        r ∈ C i → s ∈ C i → s ⊆ r → r ∈ Φ A → s ∈ Φ A) ∧
      (∀ i,
        ∃ b, b ∈ C i ∧ (∀ r ∈ C i, b ⊆ r) ∧
          (F.filter (fun A => b ∈ Φ A)).card =
            (F.filter (fun A => i ∈ S A)).card)

end MathlibPlus.Open.FormalizationBatch
