import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics.Claim26688

/-- An inclusion-minimal member containing a fixed coordinate can be removed
from a finite union-closed family without breaking union-closure. -/
theorem coordinate_minimal_removable
    {X : Type*} (F : Set (Set X)) (x : X) (M : Set X)
    (_hfinite : F.Finite)
    (h_union : ∀ ⦃A : Set X⦄, A ∈ F → ∀ ⦃B : Set X⦄, B ∈ F → A ∪ B ∈ F)
    (_hM : M ∈ F) (hxM : x ∈ M)
    (hmin : ∀ ⦃N : Set X⦄, N ∈ F → x ∈ N → N ⊆ M → N = M) :
    ∀ ⦃A : Set X⦄, A ∈ F \ {M} →
      ∀ ⦃B : Set X⦄, B ∈ F \ {M} → A ∪ B ∈ F \ {M} := by
  intro A hA B hB
  have hU : A ∪ B ∈ F := h_union hA.1 hB.1
  refine ⟨hU, ?_⟩
  intro hUM
  have hxU : x ∈ A ∪ B := by
    rw [hUM]
    exact hxM
  rcases hxU with hxA | hxB
  · have hAsub : A ⊆ M := by
      intro y hy
      have hyU : y ∈ A ∪ B := Or.inl hy
      rw [← hUM]
      exact hyU
    have hAe : A = M := hmin hA.1 hxA hAsub
    exact hA.2 (by simp [hAe])
  · have hBsub : B ⊆ M := by
      intro y hy
      have hyU : y ∈ A ∪ B := Or.inr hy
      rw [← hUM]
      exact hyU
    have hBe : B = M := hmin hB.1 hxB hBsub
    exact hB.2 (by simp [hBe])

end MathlibPlus.Combinatorics.Claim26688
