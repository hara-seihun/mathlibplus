import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- The alternating group on four letters has a genuinely simultaneous
binary-relational Cayley defect with only two disjoint relation symbols.
Each coordinate separately has a group-automorphism transporter, but no one
group automorphism transports both coordinates. -/
def alternatingFourTwoRelationSimultaneousDefect : Prop :=
  let G := alternatingGroup (Fin 4)
  ∃ (S T : Fin 2 → Set G) (q : G ≃ G),
    q 1 = 1 ∧
    q.symm = q ∧
    (∀ i, 1 ∉ S i ∧ 1 ∉ T i) ∧
    T = (fun i => q '' S i) ∧
    Set.ncard (S 0) = 1 ∧ Set.ncard (T 0) = 1 ∧
    Set.ncard (S 1) = 5 ∧ Set.ncard (T 1) = 5 ∧
    Disjoint (S 0) (S 1) ∧ Disjoint (T 0) (T 1) ∧
    (∀ i x y, x⁻¹ * y ∈ S i ↔ (q x)⁻¹ * q y ∈ T i) ∧
    (∀ i, ∃ α : G ≃* G, α '' S i = T i) ∧
    ¬ ∃ α : G ≃* G, ∀ i, α '' S i = T i

end MathlibPlus.Open.GraphTheory
