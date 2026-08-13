import Mathlib

namespace MathlibPlus.LinearAlgebra

/-- The displayed two-vector Jordan relation yields a nilpotent remainder on its span. -/
theorem microscopicJordanRelation_claim10825
    {R V : Type*} [Field R] [AddCommGroup V] [Module R V]
    (A : V →ₗ[R] V) (Khat P : V) (Delta a b : R)
    (hK : A Khat = Delta • Khat + (a * b) • P)
    (hP : A P = Delta • P) :
    ∃ N : V →ₗ[R] V,
      A = Delta • LinearMap.id + N ∧
      N Khat = (a * b) • P ∧
      N P = 0 ∧
      ∀ v ∈ Submodule.span R ({Khat, P} : Set V), N (N v) = 0 := by
  let N : V →ₗ[R] V := A - Delta • LinearMap.id
  have hA : A = Delta • LinearMap.id + N := by
    dsimp [N]
    abel
  have hNK : N Khat = (a * b) • P := by
    dsimp [N]
    rw [hK]
    simp
  have hNP : N P = 0 := by
    dsimp [N]
    rw [hP]
    simp
  have hN2K : (N.comp N) Khat = 0 := by
    simp [LinearMap.comp_apply, hNK, hNP]
  have hN2P : (N.comp N) P = 0 := by
    simp [LinearMap.comp_apply, hNP]
  have hker : Submodule.span R ({Khat, P} : Set V) ≤ (N.comp N).ker := by
    refine Submodule.span_le.2 ?_
    intro v hv
    have hv' : v = Khat ∨ v = P := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hv
    rcases hv' with h | h
    · change (N.comp N) v = 0
      rw [h]
      exact hN2K
    · change (N.comp N) v = 0
      rw [h]
      exact hN2P
  refine ⟨N, hA, hNK, hNP, ?_⟩
  intro v hv
  exact hker hv

end MathlibPlus.LinearAlgebra
