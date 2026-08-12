import Mathlib

namespace MathlibPlus.LinearAlgebra

/-- Claim 20138, with the grading reindexed so that the raising maps go from
`V (n₀ + d)` to `V (n₀ + d + 1)`. -/
theorem claim20138_joint_raising_iff_cyclic_words
    (V : ℕ → Type*) [∀ n, AddCommGroup (V n)] [∀ n, Module ℚ (V n)]
    (n₀ : ℕ) (e : V n₀) (k : ℕ)
    (G : ∀ n, Fin k → V n →ₗ[ℚ] V (n + 1))
    (hbottom : Submodule.span ℚ ({e} : Set (V n₀)) = ⊤) :
    (∀ d : ℕ,
      Submodule.span ℚ (⋃ i : Fin k, Set.range (G (n₀ + d) i)) = ⊤) ↔
      (∀ d : ℕ,
        (Nat.rec (motive := fun d => Submodule ℚ (V (n₀ + d)))
          (Submodule.span ℚ ({e} : Set (V n₀)))
          (fun d W =>
            Submodule.span ℚ
              (⋃ i : Fin k,
                (G (n₀ + d) i) '' (W : Set (V (n₀ + d))))) d = ⊤)) := by
  constructor
  · intro hR d
    induction d with
    | zero => simpa using hbottom
    | succ d ih =>
        simpa [ih] using hR d
  · intro hC d
    apply top_unique
    rw [← hC (d + 1)]
    change
      Submodule.span ℚ
          (⋃ i : Fin k,
            (G (n₀ + d) i) ''
              ((Nat.rec (motive := fun d => Submodule ℚ (V (n₀ + d)))
                (Submodule.span ℚ ({e} : Set (V n₀)))
                (fun d W =>
                  Submodule.span ℚ
                    (⋃ i : Fin k,
                      (G (n₀ + d) i) '' (W : Set (V (n₀ + d))))) d :
                Submodule ℚ (V (n₀ + d))) : Set (V (n₀ + d)))) ≤
        Submodule.span ℚ (⋃ i : Fin k, Set.range (G (n₀ + d) i))
    apply Submodule.span_mono
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨i, ⟨y, hy, rfl⟩⟩
    exact Set.mem_iUnion.mpr ⟨i, ⟨y, rfl⟩⟩

end MathlibPlus.LinearAlgebra
