import Mathlib

namespace MathlibPlus.Algebra.Claim6571And25683

/-- Claim 25683: the exact integer coordinate-deficit update under a
removable deletion, together with its even/odd strict-minority consequences. -/
def coordinateDeficit_erase : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (A : Finset α) (x : α),
    A ∈ F →
    (∀ B ∈ F, ∀ C ∈ F, B ∪ C ∈ F) →
    (∀ B ∈ F.erase A, ∀ C ∈ F.erase A, B ∪ C ∈ F.erase A) →
    (∀ y : α, 2 * (F.filter (fun B => y ∈ B)).card < F.card) →
    let deficit : α → ℤ := fun y =>
      (F.card : ℤ) - 2 * ((F.filter (fun B => y ∈ B)).card : ℤ)
    let erasedDeficit : α → ℤ := fun y =>
      ((F.erase A).card : ℤ) -
        2 * (((F.erase A).filter (fun B => y ∈ B)).card : ℤ)
    (erasedDeficit x = deficit x - 1 + 2 * if x ∈ A then 1 else 0) ∧
      (Even F.card →
        ∀ y : α, 2 * ((F.erase A).filter (fun B => y ∈ B)).card <
          (F.erase A).card) ∧
      (Odd F.card →
        ((∀ y : α, 2 * ((F.erase A).filter (fun B => y ∈ B)).card <
            (F.erase A).card) ↔
          (∀ y : α, deficit y = 1 → y ∈ A)))

end MathlibPlus.Algebra.Claim6571And25683
