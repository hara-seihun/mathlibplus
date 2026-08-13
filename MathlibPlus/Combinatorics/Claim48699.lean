import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic

namespace MathlibPlus.Combinatorics

/--
Claim 48699: a principal-ideal description of the members omitting `x`
implies both the displayed set equality and the resulting cardinality
identity.  The finite family and the witness `r` make the source's
`𝓕` and `r_x` explicit.
-/
theorem principalIdealIdentity_claim48699
    {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (x : α) (r : Finset α)
    (hprincipal : ∀ A ∈ F, x ∉ A ↔ A ⊆ r) :
    F.filter (fun A => x ∉ A) = F.filter (fun A => A ⊆ r) ∧
      (F.filter (fun A => x ∈ A)).card =
        F.card - (F.filter (fun A => A ⊆ r)).card := by
  classical
  have hset : F.filter (fun A => x ∉ A) = F.filter (fun A => A ⊆ r) := by
    apply Finset.filter_congr
    intro A hA
    exact hprincipal A hA
  have hcard :
      (F.filter (fun A => x ∈ A)).card +
          (F.filter (fun A => x ∉ A)).card = F.card := by
    exact Finset.card_filter_add_card_filter_not (s := F)
      (p := fun A : Finset α => x ∈ A)
  rw [hset] at hcard
  exact ⟨hset, Nat.eq_sub_of_add_eq hcard⟩

end MathlibPlus.Combinatorics
