import MathlibPlus.Open.Combinatorics.TraceAndCayleyBatch

namespace MathlibPlus.Open.Combinatorics.Claim3376

open MathlibPlus.Open.Combinatorics.Claim3374

/--
Claim 3376: in the exactly-three-tight branch, removable singleton traces
pairwise union to the three two-point traces, and no member with a two-point
trace is removable.
-/
def twoPointTraceMembersAreNonremovable : Prop :=
  ∀ (n : ℕ) (F : Finset (Finset (Fin n))),
    minimumFranklCounterexample F →
    (tightSet F).card = 3 →
      (∀ A, A ∈ F → removable F A →
        (A ∩ tightSet F).card ≤ 1) ∧
      (∀ x, x ∈ tightSet F →
        ∃ A, A ∈ F ∧ removable F A ∧
          A ∩ tightSet F = {x}) ∧
      (∀ {x y : Fin n}, x ∈ tightSet F → y ∈ tightSet F → x ≠ y →
        ∃ A B,
          A ∈ F ∧ B ∈ F ∧
          removable F A ∧ removable F B ∧
          A ∩ tightSet F = {x} ∧
          B ∩ tightSet F = {y} ∧
          A ∪ B ∈ F ∧
          (A ∪ B) ∩ tightSet F = {x, y} ∧
          (∀ M, M ∈ F → M ∩ tightSet F = {x, y} →
            ¬ removable F M))

end MathlibPlus.Open.Combinatorics.Claim3376
