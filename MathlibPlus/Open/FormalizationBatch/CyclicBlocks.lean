import Mathlib

namespace MathlibPlus.Open.FormalizationBatch.CyclicBlocks

noncomputable def cyclicRegularActionBlockSystems : Prop :=
  ∀ (p q : ℕ) (G Ω : Type*)
    [Group G] [Fintype G] [Fintype Ω] [MulAction G Ω],
    Nat.Prime p →
      Nat.Prime q →
        p ≠ q →
          Nat.card G = p * q →
            IsCyclic G →
              (Nonempty Ω ∧ ∀ x y : Ω, ∃! g : G, g • x = y) →
                let actionImage :=
                  fun (g : G) (B : Set Ω) =>
                    {y | ∃ x, x ∈ B ∧ g • x = y}
                let isBlockSystem :=
                  fun (P : Set (Set Ω)) =>
                    (∀ B ∈ P, B.Nonempty) ∧
                      (∀ x : Ω, ∃ B, B ∈ P ∧ x ∈ B) ∧
                        (∀ B₁ ∈ P, ∀ B₂ ∈ P,
                          B₁ ≠ B₂ → Disjoint B₁ B₂) ∧
                          (∀ g : G, ∀ B ∈ P, actionImage g B ∈ P)
                let nontrivial :=
                  fun (P : Set (Set Ω)) =>
                    P ≠ ({Set.univ} : Set (Set Ω)) ∧
                      ¬(∀ B ∈ P, ∀ x ∈ B, ∀ y ∈ B, x = y)
                let cellSize :=
                  fun (P : Set (Set Ω)) (r : ℕ) =>
                    ∀ B ∈ P, Nat.card {x : Ω // x ∈ B} = r
                let characteristic :=
                  fun (K : Subgroup G) =>
                    ∀ φ : G ≃* G,
                      Set.image (fun x : G => φ x) (K : Set G) = (K : Set G)
                let orbitSystem :=
                  fun (K : Subgroup G) =>
                    {B | ∃ x : Ω,
                      B = {y | ∃ k : G, k ∈ (K : Set G) ∧ k • x = y}}
                (∀ P : Set (Set Ω),
                    isBlockSystem P →
                      nontrivial P →
                        ∃ r : ℕ, (r = p ∨ r = q) ∧ cellSize P r) ∧
                  (∀ r : ℕ, (r = p ∨ r = q) →
                    (∃! K : Subgroup G,
                        characteristic K ∧ Nat.card K = r) ∧
                      (∃! P : Set (Set Ω),
                        isBlockSystem P ∧
                          cellSize P r ∧
                            ∃ K : Subgroup G,
                              characteristic K ∧
                                Nat.card K = r ∧
                                  P = orbitSystem K))

end MathlibPlus.Open.FormalizationBatch.CyclicBlocks
