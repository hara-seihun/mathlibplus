import Mathlib

namespace MathlibPlus.LinearAlgebra

/-- The affine fibre of a linear map is a translate of its kernel.  This is
 the abstract linear-algebra content of the off-path detour identity in claim
 56964; the graph/path presentation is intentionally not encoded here. -/
theorem affine_fiber_eq_translate_kernel_claim56964
    {𝕜 V W : Type*} [Ring 𝕜] [AddCommGroup V] [AddCommGroup W]
    [Module 𝕜 V] [Module 𝕜 W] (D : V →ₗ[𝕜] W) (b d₀ : V)
    (h₀ : D d₀ = D b) :
    {d : V | D d = D b} =
      (fun k : V => d₀ + k) '' (LinearMap.ker D : Set V) := by
  ext d
  constructor
  · intro hd
    change D d = D b at hd
    refine ⟨d - d₀, ?_, ?_⟩
    · change D (d - d₀) = 0
      simp [hd, h₀]
    · simp
  · rintro ⟨k, hk, rfl⟩
    change D k = 0 at hk
    change D (d₀ + k) = D b
    simp [hk, h₀]

/-- Two points have the same linear boundary exactly when their difference is
an element of the kernel. -/
theorem affine_fiber_difference_mem_kernel_iff_claim56964
    {𝕜 V W : Type*} [Ring 𝕜] [AddCommGroup V] [AddCommGroup W]
    [Module 𝕜 V] [Module 𝕜 W] (D : V →ₗ[𝕜] W) (d e : V) :
    D d = D e ↔ d - e ∈ (LinearMap.ker D : Set V) := by
  change D d = D e ↔ D (d - e) = 0
  constructor
  · intro h
    simp [h]
  · intro h
    have h' : D d - D e = 0 := by simpa using h
    exact sub_eq_zero.mp h'

end MathlibPlus.LinearAlgebra

namespace MathlibPlus.Algebra

/-- A finite typed direct-sum vector can be nonzero even when its erasure sums
all coordinates to zero.  The finite function is represented by a `Finsupp`;
this is the type-erasure content of claim 51976. -/
theorem typed_vector_nonzero_of_centered_claim51976
    {R ι : Type*} [Semiring R] [Fintype ι] [Nonempty ι]
    (c F : ι → R) (hprod : ∀ i, c i * F i ≠ 0)
    (hcenter : ∑ i, c i * F i = 0) :
    let v : ι →₀ R := Finsupp.equivFunOnFinite.symm (fun i => c i * F i)
    v ≠ 0 ∧ ∑ i, v i = 0 := by
  dsimp
  constructor
  · intro hv
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    have hi := congrArg (fun g : ι →₀ R => g i) hv
    exact hprod i (by simpa using hi)
  · simpa using hcenter

end MathlibPlus.Algebra

namespace MathlibPlus.LinearAlgebra

/-- The normalized upper-unitriangular two-by-two local map has the repeated
unit root recorded in the characteristic-polynomial subclaim of claim 46497.
The conductor and reciprocity interpretation remain outside this abstract
matrix statement. -/
theorem normalized_removed_prime_map_charpoly_claim46497
    (a c : ℝ) (_ha : |a| ≤ c) :
    Matrix.charpoly (!![(1 : ℝ), a; 0, 1]) =
      (Polynomial.X - Polynomial.C 1) ^ 2 := by
  rw [Matrix.charpoly_fin_two, Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
  norm_num
  have hC2 : (Polynomial.C (2 : ℝ) : Polynomial ℝ) = 2 := by
    ext n
    cases n with
    | zero => simp [Polynomial.coeff_C]
    | succ n => simp [Polynomial.coeff_natCast_ite]
  rw [hC2]
  ring

end MathlibPlus.LinearAlgebra
