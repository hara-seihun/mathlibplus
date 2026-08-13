import MathlibPlus.NumberTheory.Claim3156
import MathlibPlus.NumberTheory.Claim35665

open scoped BigOperators

namespace MathlibPlus.NumberTheory.Claim44246

open MathlibPlus.NumberTheory

noncomputable section

/-- The known consecutive-block family yields infinitely many positive represented indices. -/
theorem infinitely_many_positive_representable_indices :
    Set.Infinite {n : ℕ |
      ∃ m : ℕ, 2 ≤ m ∧
        n = 2 ^ (m + 1) - m - 2 ∧
        0 < n ∧
        MathlibPlus.NumberTheory.Claim3156.weight n =
          ∑ d ∈ Finset.range m,
            MathlibPlus.NumberTheory.Claim3156.weight (n + d + 1)} := by
  let f : ℕ → ℕ := fun m => 2 ^ (m + 1) - m - 2
  have hf : StrictMono f := by
    simpa [f] using
      MathlibPlus.NumberTheory.claim35665_consecutiveDyadicRepresentations.1
  have hfi : Function.Injective (fun k : ℕ => f (k + 2)) := by
    intro a b hab
    have hab' : a + 2 = b + 2 := hf.injective hab
    omega
  apply Set.infinite_of_injective_forall_mem hfi
  intro k
  have hpow_lower : ∀ m : ℕ, 2 ≤ m → m + 5 ≤ 2 ^ (m + 1) := by
    intro m hm
    induction m with
    | zero => omega
    | succ m ih =>
        by_cases hsmall : m < 2
        · have hm_eq : m = 1 := by omega
          subst m
          norm_num
        · have ihm : m + 5 ≤ 2 ^ (m + 1) := ih (by omega)
          rw [show Nat.succ m + 1 = (m + 1) + 1 by omega, pow_succ]
          omega
  have hpow_lower_k : (k + 2) + 5 ≤ 2 ^ ((k + 2) + 1) :=
    hpow_lower (k + 2) (by omega)
  have hn : 0 < f (k + 2) := by
    dsimp [f]
    omega
  have h := (MathlibPlus.NumberTheory.claim35665_consecutiveDyadicRepresentations).2
    (k + 2) (by omega)
  dsimp at h
  rcases h with ⟨hrel, hsum⟩
  dsimp [f]
  refine ⟨k + 2, by omega, rfl, hn, ?_⟩
  simpa [MathlibPlus.NumberTheory.Claim3156.weight, Nat.add_assoc] using hsum.symm

end
end MathlibPlus.NumberTheory.Claim44246
