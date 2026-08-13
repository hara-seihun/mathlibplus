import Mathlib

open Filter Topology Module
open scoped InnerProductSpace

namespace MathlibPlus.Analysis.Claim3917

/-- Claim 3917: orthogonal projection onto a finite-dimensional subspace sends a
bounded weakly-null sequence to a norm-null sequence.  Weak nullity is written
using all continuous linear functionals, and the boundedness hypothesis is
retained from the source (the finite-dimensional argument only uses weak
nullity). -/
theorem finiteDimensionalProjection_tendsto_zero
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (x : ℕ → E)
    (_hbounded : ∃ C : ℝ, ∀ n, ‖x n‖ ≤ C)
    (hweak : ∀ φ : E →L[𝕜] 𝕜,
      Tendsto (fun n => φ (x n)) atTop (𝓝 0))
    (U : Submodule 𝕜 E) [FiniteDimensional 𝕜 U] :
    Tendsto (fun n => (U.orthogonalProjectionOnto (x n) : E)) atTop (𝓝 0) := by
  let b : OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 U :=
    stdOrthonormalBasis 𝕜 U
  have hcoeff : ∀ i : Fin (finrank 𝕜 U),
      Tendsto (fun n => ‖⟪b i, U.orthogonalProjectionOnto (x n)⟫_𝕜‖)
        atTop (𝓝 0) := by
    intro i
    have hi := tendsto_norm.comp (hweak (innerSL 𝕜 (b i : E)))
    simpa only [norm_zero] using
      (hi.congr' (Filter.Eventually.of_forall (fun n =>
        congrArg norm
          (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (b i) (x n)).symm)))
  have hsum : Tendsto
      (fun n => ∑ i : Fin (finrank 𝕜 U),
        ‖⟪b i, U.orthogonalProjectionOnto (x n)⟫_𝕜‖)
      atTop (𝓝 0) := by
    simpa using
      (tendsto_finsetSum (Finset.univ : Finset (Fin (finrank 𝕜 U)))
        (fun i _ => hcoeff i))
  have hle : ∀ n,
      ‖(U.orthogonalProjectionOnto (x n) : E)‖ ≤
        ∑ i : Fin (finrank 𝕜 U),
          ‖⟪b i, U.orthogonalProjectionOnto (x n)⟫_𝕜‖ := by
    intro n
    have hr := b.sum_repr' (U.orthogonalProjectionOnto (x n))
    calc
      ‖(U.orthogonalProjectionOnto (x n) : E)‖ =
          ‖∑ i : Fin (finrank 𝕜 U),
            ⟪b i, U.orthogonalProjectionOnto (x n)⟫_𝕜 • b i‖ := by
          rw [hr]
          simp [Submodule.coe_norm]
      _ ≤ ∑ i : Fin (finrank 𝕜 U),
            ‖⟪b i, U.orthogonalProjectionOnto (x n)⟫_𝕜 • b i‖ := by
          simpa using
            (norm_sum_le (Finset.univ : Finset (Fin (finrank 𝕜 U)))
              (fun i => ⟪b i, U.orthogonalProjectionOnto (x n)⟫_𝕜 • b i))
      _ = ∑ i : Fin (finrank 𝕜 U),
            ‖⟪b i, U.orthogonalProjectionOnto (x n)⟫_𝕜‖ := by
          simp [norm_smul, b.norm_eq_one]
  apply (tendsto_zero_iff_norm_tendsto_zero).2
  exact squeeze_zero' (Filter.Eventually.of_forall (fun n => norm_nonneg _))
    (Filter.Eventually.of_forall (fun n => hle n)) hsum

end MathlibPlus.Analysis.Claim3917
