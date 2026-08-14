import Mathlib

namespace MathlibPlus.Open

/-- Claim 49289: the three-coordinate majority lemma and its empty-only exception. -/
def claim49289 {α : Type*} [DecidableEq α] : Prop :=
  ∀ (T : Finset α) (H : Finset (Finset α)),
    T.card = 3 →
    H.Nonempty →
    (∀ S ∈ H, S ⊆ T) →
    (∀ S ∈ H, ∀ R ∈ H, S ∪ R ∈ H) →
    ((∃ S ∈ H, S.Nonempty) →
      ∃ i ∈ T, 2 * (H.filter (fun S => i ∈ S)).card ≥ H.card) ∧
    (H = {∅} →
      ∀ i ∈ T, (H.filter (fun S => i ∈ S)).card = 0)

end MathlibPlus.Open
