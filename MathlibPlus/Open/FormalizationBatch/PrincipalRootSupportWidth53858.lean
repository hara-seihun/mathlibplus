import Mathlib

namespace MathlibPlus.Open.FormalizationBatch

private def principalZeroRoot53858
    {α : Type} [DecidableEq α]
    (F : Finset (Finset α)) (x : α) : Finset α :=
  (F.filter (fun A => x ∉ A)).biUnion (fun A : Finset α => A)

private def distinctPrincipalZeroRoots53858
    {α : Type} [DecidableEq α]
    (F : Finset (Finset α)) (X : Finset α) : Finset (Finset α) :=
  X.biUnion (fun x => {principalZeroRoot53858 F x})

private def compressedRootSet53858
    {α : Type} [DecidableEq α]
    (F : Finset (Finset α)) (X : Finset α)
    (A : Finset α) : Finset (Finset α) :=
  (distinctPrincipalZeroRoots53858 F X).filter (fun r => ¬ A ⊆ r)

private def chainSupport53858
    {α : Type} [DecidableEq α]
    (F : Finset (Finset α)) (X : Finset α)
    (t : ℕ) (C : Fin t → Finset (Finset α))
    (A : Finset α) : Finset (Fin t) :=
  Finset.univ.filter (fun i =>
    (compressedRootSet53858 F X A ∩ C i).Nonempty)

private def principalRootChainPartition53858
    {α : Type} [DecidableEq α]
    (F : Finset (Finset α)) (X : Finset α)
    (t : ℕ) (C : Fin t → Finset (Finset α)) : Prop :=
  (∀ i, (C i).Nonempty) ∧
    (∀ i r s, r ∈ C i → s ∈ C i → r ⊆ s ∨ s ⊆ r) ∧
    (∀ i r, r ∈ C i →
      r ∈ distinctPrincipalZeroRoots53858 F X) ∧
    (∀ r, r ∈ distinctPrincipalZeroRoots53858 F X →
      ∃! i, r ∈ C i)

private def minimumNonemptySupport53858
    {α : Type} [DecidableEq α]
    (F : Finset (Finset α)) (X : Finset α)
    (t : ℕ) (C : Fin t → Finset (Finset α))
    (σ : ℕ) : Prop :=
  (∃ A ∈ F,
      (chainSupport53858 F X t C A).Nonempty ∧
        (chainSupport53858 F X t C A).card = σ) ∧
    (∀ A ∈ F,
      (chainSupport53858 F X t C A).Nonempty →
        σ ≤ (chainSupport53858 F X t C A).card)

private def noHalfFrequency53858
    {α : Type} [DecidableEq α]
    (F : Finset (Finset α)) (X : Finset α) : Prop :=
  ∀ x ∈ X,
    2 * (F.filter (fun A => x ∈ A)).card < F.card

private def halfFrequency53858
    {α : Type} [DecidableEq α]
    (F : Finset (Finset α)) (X : Finset α) : Prop :=
  ∃ x ∈ X,
    2 * (F.filter (fun A => x ∈ A)).card ≥ F.card

/-- Claim 53858: the principal-root minimum-support bound, the separate
    equality-case exclusion and payload, the six-chain consequence, and the
    resulting lower bound on every counterexample's chain-cover width. -/
def principalRootSupportWidth53858 : Prop :=
  (∀ {α : Type} [DecidableEq α]
    (F : Finset (Finset α)) (X : Finset α),
    (∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F) →
    X = F.biUnion (fun A : Finset α => A) →
    (∀ x ∈ X, ∃ A ∈ F, x ∉ A) →
    ∀ (t : ℕ) (C : Fin t → Finset (Finset α)),
      principalRootChainPartition53858 F X t C →
      ∀ σ : ℕ,
        noHalfFrequency53858 F X →
        minimumNonemptySupport53858 F X t C σ →
        3 ≤ σ ∧ t ≥ 2 * σ + 1) ∧
  (∀ {α : Type} [DecidableEq α]
    (F : Finset (Finset α)) (X : Finset α),
    (∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F) →
    X = F.biUnion (fun A : Finset α => A) →
    (∀ x ∈ X, ∃ A ∈ F, x ∉ A) →
    ∀ (t : ℕ) (C : Fin t → Finset (Finset α)),
      principalRootChainPartition53858 F X t C →
      ∀ σ : ℕ,
        noHalfFrequency53858 F X →
        minimumNonemptySupport53858 F X t C σ →
        t = 2 * σ →
        (Even F.card → False) ∧
        (Odd F.card →
          (∃ A₀ ∈ F,
            chainSupport53858 F X t C A₀ = ∅ ∧
              (∀ A ∈ F,
                chainSupport53858 F X t C A = ∅ ↔ A = A₀) ∧
              (∀ A ∈ F, A ≠ A₀ →
                (chainSupport53858 F X t C A).card = σ)) ∧
          (∀ i,
            (F.filter (fun A => i ∈ chainSupport53858 F X t C A)).card =
              (F.card - 1) / 2) ∧
          (∀ A ∈ F, ∀ B ∈ F,
            chainSupport53858 F X t C (A ∪ B) =
              chainSupport53858 F X t C A ∪
                chainSupport53858 F X t C B) ∧
          (∀ A ∈ F, ∀ B ∈ F,
            (chainSupport53858 F X t C A).Nonempty →
              (chainSupport53858 F X t C B).Nonempty →
              chainSupport53858 F X t C A =
                chainSupport53858 F X t C B) ∧
          (∃ I : Finset (Fin t), I.card = σ ∧
            ∀ i ∈ I, ∀ A ∈ F,
              i ∉ chainSupport53858 F X t C A))) ∧
  (∀ {α : Type} [DecidableEq α]
    (F : Finset (Finset α)) (X : Finset α),
    (∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F) →
    X = F.biUnion (fun A : Finset α => A) →
    ∀ (t : ℕ) (C : Fin t → Finset (Finset α)),
      principalRootChainPartition53858 F X t C →
      t ≤ 6 →
      halfFrequency53858 F X) ∧
  (∀ {α : Type} [DecidableEq α]
    (F : Finset (Finset α)) (X : Finset α),
    (∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F) →
    X = F.biUnion (fun A : Finset α => A) →
    ∀ (t : ℕ) (C : Fin t → Finset (Finset α)),
      principalRootChainPartition53858 F X t C →
      noHalfFrequency53858 F X →
      7 ≤ t)

end MathlibPlus.Open.FormalizationBatch
