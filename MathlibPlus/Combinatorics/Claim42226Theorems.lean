import MathlibPlus.Combinatorics.Claim42226Definitions
import Mathlib.Data.Set.Finite.Basic

namespace MathlibPlus.Combinatorics.Claim42226

variable {α : Type*} [DecidableEq α]

/-- Removing the same fixed set from a union-closed finite family preserves
union-closure and finiteness. -/
theorem outsideSupport_finite_unionClosed
    (F : Set (Finset α)) (hFfin : F.Finite)
    (hFunion : ∀ ⦃A B : Finset α⦄, A ∈ F → B ∈ F → A ∪ B ∈ F)
    (M : Finset α) :
    let Sigma : Set (Finset α) := outsideSupport M '' F
    Sigma.Finite ∧
      (∀ ⦃A B : Finset α⦄, A ∈ Sigma → B ∈ Sigma → A ∪ B ∈ Sigma) := by
  dsimp
  constructor
  · exact hFfin.image _
  · rintro A B ⟨A₀, hA₀, rfl⟩ ⟨B₀, hB₀, rfl⟩
    refine ⟨A₀ ∪ B₀, hFunion hA₀ hB₀, ?_⟩
    simp only [outsideSupport, Finset.union_sdiff_distrib]

end MathlibPlus.Combinatorics.Claim42226
