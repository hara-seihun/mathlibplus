import Mathlib

namespace MathlibPlus.Combinatorics.Claim45133

/-- Claim 45133: the union-with-M trace fibers form the exact disjoint
union decomposition, and each fiber is union-closed and contains M. -/
def unionClosed_traceFiber_bijective : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (M : Finset α),
    M ∈ F →
    (∀ ⦃A B : Finset α⦄, A ∈ F → B ∈ F → A ∪ B ∈ F) →
    let U := F.filter (fun G => M ⊆ G)
    let H := fun G : Finset α =>
      (F.filter (fun A => A ∪ M = G)).image (fun A => A ∩ M)
    let D := Σ G : {G // G ∈ U}, {T // T ∈ H G}
    (∃ e : {A // A ∈ F} ≃ D,
      ∀ A : {A // A ∈ F},
        (e A).1.1 = A.1 ∪ M ∧
          (e A).2.1 = A.1 ∩ M) ∧
      (∀ G, G ∈ U → M ∈ H G) ∧
      (∀ G, G ∈ U →
        ∀ ⦃T₁ T₂⦄, T₁ ∈ H G → T₂ ∈ H G → T₁ ∪ T₂ ∈ H G)

end MathlibPlus.Combinatorics.Claim45133
