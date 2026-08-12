import Mathlib

namespace MathlibPlus.NumberTheory

/-- Re-indexing `m = n - k` turns the full target range into the displayed
shift range.  The `sup'` in the left-hand side is the exact maximum defining
`D(n)` on the nonempty interval `1 ≤ m < n`. -/
theorem target_bound_shift_iff_claim45358
    (τ : ℤ → ℤ) {n : ℤ} (hn : 2 ≤ n) :
    let M : Finset ℤ := Finset.Icc 1 (n - 1)
    let hM : M.Nonempty := by
      refine ⟨1, ?_⟩
      simp only [M, Finset.mem_Icc]
      omega
    let D : ℤ := M.sup' hM (fun m => m + τ m)
    D ≤ n + 2 ↔
      ∀ k : ℤ, 1 ≤ k → k < n → τ (n - k) ≤ k + 2 := by
  let M : Finset ℤ := Finset.Icc 1 (n - 1)
  have hM : M.Nonempty := by
    refine ⟨1, ?_⟩
    simp only [M, Finset.mem_Icc]
    omega
  change M.sup' hM (fun m => m + τ m) ≤ n + 2 ↔ _
  rw [Finset.sup'_le_iff hM]
  constructor
  · intro h k hk₁ hkn
    have hm : n - k ∈ M := by
      simp only [M, Finset.mem_Icc]
      omega
    have hm' := h (n - k) hm
    omega
  · intro h m hm
    have hm' : 1 ≤ m ∧ m ≤ n - 1 := by
      simpa only [M, Finset.mem_Icc] using hm
    have hk₁ : 1 ≤ n - m := by omega
    have hkn : n - m < n := by omega
    have hk0 := h (n - m) hk₁ hkn
    have hk : τ m ≤ n - m + 2 := by
      simpa only [sub_sub_cancel] using hk0
    omega

end MathlibPlus.NumberTheory
