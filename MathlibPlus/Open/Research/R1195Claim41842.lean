import Mathlib
import MathlibPlus.Open.ResearchBatchHallControls

namespace MathlibPlus.Open.Research.R1195

open MathlibPlus.Open.ResearchBatchHallControls

/-- Actual quotient permutations are exactly those induced by graph
automorphisms in the setwise stabilizer of the common Hall block system. -/
def claim41842 : Prop :=
  ∀ m : ℕ, 1 < m → Odd m → Squarefree m → ¬ (3 ∣ m) →
    ∀ Γ : SimpleGraph (Gm m),
      let B : Set (Set (Gm m)) := hallPartition m
      let A : Set (Equiv.Perm (Gm m)) :=
        {a | ∀ x y, Γ.Adj x y ↔ Γ.Adj (a x) (a y)}
      let A_B : Set (Equiv.Perm (Gm m)) :=
        {a | a ∈ A ∧
          Set.image (fun C : Set (Gm m) => a '' C) B = B}
      let πA_B : Set (Equiv.Perm (ZMod 8)) :=
        {q | ∃ a, a ∈ A_B ∧
          ∀ i : ZMod 8, a '' hallBlock m i = hallBlock m (q i)}
      ∀ q : Equiv.Perm (ZMod 8),
        q ∈ πA_B ↔
          ∃ a, a ∈ A ∧
            Set.image (fun C : Set (Gm m) => a '' C) B = B ∧
            (∀ i : ZMod 8,
              a '' hallBlock m i = hallBlock m (q i))

end MathlibPlus.Open.Research.R1195
