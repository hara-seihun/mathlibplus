import Mathlib

namespace MathlibPlus.Analysis.Claim3947

/-- If a uniformly bounded sequence of continuous linear operators is applied to a
bounded sequence of inputs, its output sequence is bounded.  In a finite-dimensional
real or complex target this also makes the output range relatively compact. -/
theorem finiteDimensional_output_corollary_claim3947
    {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [FiniteDimensional 𝕜 Y]
    (T : ℕ → X →L[𝕜] Y) (u : ℕ → X)
    (hT : BddAbove (Set.range (fun j => ‖T j‖)))
    (hu : ∀ j, ‖u j‖ ≤ 1) :
    Bornology.IsBounded (Set.range (fun j => T j (u j))) ∧
      IsCompact (closure (Set.range (fun j => T j (u j)))) := by
  have hbounded : Bornology.IsBounded (Set.range (fun j => T j (u j))) := by
    rw [isBounded_iff_forall_norm_le]
    rcases bddAbove_def.mp hT with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    rintro _ ⟨j, rfl⟩
    calc
      ‖T j (u j)‖ ≤ ‖T j‖ * ‖u j‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖T j‖ * 1 :=
        mul_le_mul_of_nonneg_left (hu j) (norm_nonneg _)
      _ = ‖T j‖ := mul_one _
      _ ≤ C := hC _ ⟨j, rfl⟩
  letI := FiniteDimensional.proper_rclike 𝕜 Y
  exact ⟨hbounded, hbounded.isCompact_closure⟩

end MathlibPlus.Analysis.Claim3947
