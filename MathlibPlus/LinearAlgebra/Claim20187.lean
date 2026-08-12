import Mathlib

namespace MathlibPlus.LinearAlgebra

/--
Claim 20187.  The common kernel of adjoint weighted decks is the orthogonal
complement of the span of the weighted graft images.  The source's finite sum
of image submodules is represented by the span of their finite union; the
identity itself uses only bilinearity and nondegeneracy of the target pairing.
-/
theorem dualWeightedDeckOrthogonalDefect_claim20187
    (R V W ι : Type*) [Field R]
    [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W]
    [Fintype ι]
    (BV : V →ₗ[R] V →ₗ[R] R)
    (BW : W →ₗ[R] W →ₗ[R] R)
    (G : ι → W →ₗ[R] V)
    (L : ι → V →ₗ[R] W)
    (hW : ∀ z : W, (∀ y : W, BW z y = 0) → z = 0)
    (hadj : ∀ (f : ι) (x : V) (y : W),
      BV x (G f y) = BW (L f x) y) :
    {x : V | ∀ y : V,
      y ∈ Submodule.span R (⋃ f : ι, Set.range (G f)) → BV x y = 0} =
      {x : V | ∀ f : ι, L f x = 0} := by
  ext x
  constructor
  · intro hx f
    apply hW
    intro y
    have hy : G f y ∈ Submodule.span R (⋃ f : ι, Set.range (G f)) := by
      apply Submodule.subset_span
      exact Set.mem_iUnion.2 ⟨f, Set.mem_range.2 ⟨y, rfl⟩⟩
    have hzero := hx (G f y) hy
    rw [hadj] at hzero
    exact hzero
  · intro hx y hy
    let K : Submodule R V := LinearMap.ker (BV x)
    have hSK : Submodule.span R (⋃ f : ι, Set.range (G f)) ≤ K := by
      apply Submodule.span_le.2
      intro z hz
      rcases Set.mem_iUnion.1 hz with ⟨f, hzf⟩
      rcases Set.mem_range.1 hzf with ⟨w, rfl⟩
      change BV x (G f w) = 0
      rw [hadj]
      simp [hx f]
    exact LinearMap.mem_ker.mp (hSK hy)

end MathlibPlus.LinearAlgebra
