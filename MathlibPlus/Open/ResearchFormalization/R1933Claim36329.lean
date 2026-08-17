import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1933Claim36329

noncomputable section

private def literalSupport {α : Type*} {m : ℕ}
    [DecidableEq α] (F : Fin m → Finset α) (x : α) : Finset (Fin m) :=
  (Finset.univ : Finset (Fin m)).filter (fun i => x ∈ F i)

private def groundCarrier {α : Type*} {m : ℕ}
    [DecidableEq α] (F : Fin m → Finset α) : Finset α :=
  (Finset.univ : Finset (Fin m)).biUnion F

private def uniformDistinct {α : Type*} {m : ℕ}
    [DecidableEq α] (n : ℕ) (F : Fin m → Finset α) : Prop :=
  (∀ i, (F i).card = n) ∧ Function.Injective F

private def supportPatterns {α : Type*} {m : ℕ}
    [DecidableEq α] (F : Fin m → Finset α) : Finset (Finset (Fin m)) :=
  (groundCarrier F).image (literalSupport F)

private def laminarPatterns {α : Type*} {m : ℕ}
    [DecidableEq α] (F : Fin m → Finset α)
    (L : Finset (Finset (Fin m))) : Prop :=
  ∀ S ∈ L, ∀ T ∈ L,
    S ⊆ T ∨ T ⊆ S ∨ Disjoint S T

private def noSunflower {α : Type*} {m q : ℕ}
    [DecidableEq α] (F : Fin m → Finset α) : Prop :=
  ∀ I : Finset (Fin m), I.card = q + 1 →
    ¬ ∃ C : Finset α,
      ∀ i ∈ I, ∀ j ∈ I, i ≠ j → F i ∩ F j = C

private def matchingNumberAtMost {α : Type*} {m ν : ℕ}
    [DecidableEq α] (F : Fin m → Finset α) : Prop :=
  ∀ I : Finset (Fin m),
    (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (F i) (F j)) → I.card ≤ ν

private def pairwiseIntersecting {α : Type*} {m : ℕ}
    [DecidableEq α] (F : Fin m → Finset α) : Prop :=
  ∀ i j : Fin m, i ≠ j → (F i ∩ F j).Nonempty

/-- Claim 36329: the exact laminar-support bounds specialize at `k=3` and
    pairwise intersection, and retain the general bounded-matching estimate. -/
def pairwiseIntersectingThreeSunflowerSpecialization_claim36329 : Prop :=
  (∀ {α : Type*} [DecidableEq α]
    (m n : ℕ) (F : Fin m → Finset α),
    uniformDistinct n F →
      noSunflower (q := 2) F →
        laminarPatterns F (supportPatterns F) →
          pairwiseIntersecting F →
            matchingNumberAtMost (ν := 1) F ∧
              m ≤ 2 ^ (n - 1)) ∧
  (∀ {α : Type*} [DecidableEq α]
    (m n k ν : ℕ) (F : Fin m → Finset α),
    2 ≤ k →
      uniformDistinct n F →
        noSunflower (q := k - 1) F →
          laminarPatterns F (supportPatterns F) →
            matchingNumberAtMost (ν := ν) F →
              ν ≤ k - 2 →
                m ≤ (k - 2) * (k - 1) ^ (n - 1))

end

end MathlibPlus.Open.ResearchFormalization.R1933Claim36329
