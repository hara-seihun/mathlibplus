import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics.Claim5537

/-- The attractor waves are exactly the waves of singleton peeling: a vertex is
new at wave `k` precisely when it is not already present and all other vertices
of some incident rule have appeared at wave `k - 1`. -/
theorem attractorRecursion_equals_parallelSingletonPeeling :
    ∀ {C R : Type*} [Fintype C] [Fintype R] [DecidableEq C]
      (σ : R → Set C),
      let step : Set C → Set C := fun S ↦
        S ∪ {c | ∃ r, c ∈ σ r ∧ σ r \ {c} ⊆ S}
      let S : ℕ → Set C := fun k ↦
        Nat.rec (∅ : Set C) (fun _ s ↦ step s) k
      let winning : Set C := ⋃ k, S k
      let core : Set C := (Set.univ : Set C) \ winning
      S 0 = ∅ ∧
        (∀ k : ℕ, S (k + 1) =
          S k ∪ {c | ∃ r, c ∈ σ r ∧ σ r \ {c} ⊆ S k}) ∧
        (∀ k : ℕ, 0 < k → ∀ c : C,
          c ∈ S k \ S (k - 1) ↔
            c ∉ S (k - 1) ∧ ∃ r, c ∈ σ r ∧ σ r \ {c} ⊆ S (k - 1)) ∧
        core = (Set.univ : Set C) \ winning := by
  intro C R _ _ _ σ
  dsimp
  let step : Set C → Set C := fun S ↦
    S ∪ {c | ∃ r, c ∈ σ r ∧ σ r \ {c} ⊆ S}
  let S : ℕ → Set C := fun k ↦
    Nat.rec (∅ : Set C) (fun _ s ↦ step s) k
  let winning : Set C := ⋃ k, S k
  let core : Set C := (Set.univ : Set C) \ winning
  have hstep : ∀ k : ℕ, S (k + 1) = step (S k) := by
    intro k
    rfl
  have hzero : S 0 = (∅ : Set C) := by
    rfl
  have hwave : ∀ (k : ℕ), 0 < k → ∀ c : C,
      c ∈ S k \ S (k - 1) ↔
        c ∉ S (k - 1) ∧ ∃ r, c ∈ σ r ∧ σ r \ {c} ⊆ S (k - 1) := by
    intro k hk c
    cases k with
    | zero => omega
    | succ m =>
      simp only [Nat.succ_sub_one, Set.mem_sdiff]
      rw [hstep m]
      constructor
      · rintro ⟨hc, hnot⟩
        refine ⟨hnot, ?_⟩
        rcases hc with hc | hc
        · exact False.elim (hnot hc)
        · exact hc
      · rintro ⟨hnot, hr⟩
        exact ⟨Or.inr hr, hnot⟩
  exact ⟨hzero, (fun k ↦ by simpa [step] using hstep k), hwave, rfl⟩

end MathlibPlus.Combinatorics.Claim5537
