import Mathlib

namespace MathlibPlus
namespace LinearAlgebra

/-- Claim 50749's explicit abstract cochain calculation.  The two-dimensional
middle term is represented by functions on `Fin 2`, `delta2` is the row
`[1, 0]`, and `aStar` is `(0, 1)`. -/
theorem cohomologyDegreeTwo_claim50749 :
    let delta1 : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) := 0
    let delta2 : (Fin 2 → ℚ) →ₗ[ℚ] ℚ :=
      { toFun := fun v => v 0
        map_add' := by intro v w; rfl
        map_smul' := by intro c v; rfl }
    let aStar : Fin 2 → ℚ := ![0, 1]
    Function.comp delta2 delta1 = 0 ∧
      LinearMap.range delta1 = ⊥ ∧
      aStar ≠ 0 ∧
      delta2 aStar = 0 ∧
      LinearMap.ker delta2 = ℚ ∙ aStar ∧
      Module.finrank ℚ ((LinearMap.ker delta2) ⧸ (⊥ : Submodule ℚ (LinearMap.ker delta2))) = 1 := by
  let delta1 : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) := 0
  let delta2 : (Fin 2 → ℚ) →ₗ[ℚ] ℚ :=
    { toFun := fun v => v 0
      map_add' := by intro v w; rfl
      map_smul' := by intro c v; rfl }
  let aStar : Fin 2 → ℚ := ![0, 1]
  change Function.comp delta2 delta1 = 0 ∧
    LinearMap.range delta1 = ⊥ ∧
    aStar ≠ 0 ∧
    delta2 aStar = 0 ∧
    LinearMap.ker delta2 = ℚ ∙ aStar ∧
    Module.finrank ℚ ((LinearMap.ker delta2) ⧸ (⊥ : Submodule ℚ (LinearMap.ker delta2))) = 1
  have ha : aStar ≠ 0 := by
    intro h
    have h1 := congr_fun h 1
    norm_num [aStar] at h1
  have hker : LinearMap.ker delta2 = ℚ ∙ aStar := by
    apply Submodule.ext
    intro v
    constructor
    · intro hv
      have hv0 : v 0 = 0 := hv
      apply (Submodule.mem_span_singleton).2
      refine ⟨v 1, ?_⟩
      funext i
      fin_cases i <;> simp [aStar, hv0]
    · intro hv
      rcases (Submodule.mem_span_singleton).1 hv with ⟨c, rfl⟩
      simp [delta2, aStar]
  have hfin : Module.finrank ℚ (LinearMap.ker delta2) = 1 := by
    rw [hker]
    exact finrank_span_singleton ha
  have hquot := Submodule.finrank_quotient_add_finrank
    (⊥ : Submodule ℚ (LinearMap.ker delta2))
  refine ⟨?_, ?_, ha, ?_, hker, ?_⟩
  · ext x
    simp [delta1]
  · simp [delta1]
  · simp [delta2, aStar]
  · simpa [hfin] using hquot

end LinearAlgebra
end MathlibPlus
