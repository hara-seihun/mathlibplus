import MathlibPlus.Basic

namespace MathlibPlus.LinearAlgebra

/--
The concrete two-dimensional derivative matrix from claim 2842.  The source
first layer is the span of `v`, and the target first layer is the span of `u`
in the displayed bases, so the last conjunct is precisely failure of
filteredness for those layers.
-/
theorem canonicalFiltration_notDerivativeStable_claim2842 :
  let u : Fin 2 → ℚ := ![1, 0]
  let v : Fin 2 → ℚ := ![0, 1]
  let Φ : Matrix (Fin 2) (Fin 2) ℚ := !![12, 28; 30, 54]
  Matrix.mulVec Φ u = ![12, 30] ∧
    Matrix.mulVec Φ v = ![28, 54] ∧
    ¬ (∀ x : Fin 2 → ℚ,
      x ∈ Submodule.span ℚ ({v} : Set (Fin 2 → ℚ)) →
        Matrix.mulVec Φ x ∈ Submodule.span ℚ ({u} : Set (Fin 2 → ℚ))) := by
  dsimp
  constructor
  · ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  constructor
  · ext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · intro h
    have hv := h (![0, 1] : Fin 2 → ℚ) (by simp)
    rcases Submodule.mem_span_singleton.mp hv with ⟨c, hc⟩
    have hcoord := congrFun hc 1
    norm_num at hcoord

/--
The explicit missing-overlap-lift fixture from claim 57801, with the two
coordinate lines and their scalar-sum map written in `Fin 2 → ℚ` coordinates.
The kernel is the diagonal-difference line, while each coordinate-line
restriction has zero kernel and maps onto the scalar target.
-/
theorem missingOverlapLift_fixture_claim57801 :
  let V := Fin 2 → ℚ
  let e₁ : V := ![1, 0]
  let e₂ : V := ![0, 1]
  let C₁ : Submodule ℚ V := Submodule.span ℚ ({e₁} : Set V)
  let C₂ : Submodule ℚ V := Submodule.span ℚ ({e₂} : Set V)
  let L : V →ₗ[ℚ] ℚ :=
    { toFun := fun x => x 0 + x 1
      map_add' := by
        intro x y
        change (x 0 + y 0) + (x 1 + y 1) = (x 0 + x 1) + (y 0 + y 1)
        ring
      map_smul' := by
        intro c x
        change c * x 0 + c * x 1 = c * (x 0 + x 1)
        ring }
  (∀ x, x ∈ C₁ ↔ x 1 = 0) ∧
    (∀ x, x ∈ C₂ ↔ x 0 = 0) ∧
    (∀ x, x ∈ C₁ ∧ x ∈ C₂ ↔ x = 0) ∧
    (∀ q : ℚ, ∃ x, x ∈ C₁ ∧ L x = q) ∧
    (∀ q : ℚ, ∃ x, x ∈ C₂ ∧ L x = q) ∧
    (∀ x, x ∈ C₁ → L x = 0 → x = 0) ∧
    (∀ x, x ∈ C₂ → L x = 0 → x = 0) ∧
    (∀ x, L x = 0 ↔ ∃ c : ℚ, x = c • (e₁ - e₂)) := by
  dsimp
  have hc1 : ∀ x : Fin 2 → ℚ,
      x ∈ Submodule.span ℚ ({(![1, 0] : Fin 2 → ℚ)} : Set (Fin 2 → ℚ)) ↔ x 1 = 0 := by
    intro x
    constructor
    · intro hx
      rcases Submodule.mem_span_singleton.mp hx with ⟨c, rfl⟩
      simp [smul_apply]
    · intro hx
      rw [show x = x 0 • (![1, 0] : Fin 2 → ℚ) by
        funext i
        fin_cases i <;> simp [hx]]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have hc2 : ∀ x : Fin 2 → ℚ,
      x ∈ Submodule.span ℚ ({(![0, 1] : Fin 2 → ℚ)} : Set (Fin 2 → ℚ)) ↔ x 0 = 0 := by
    intro x
    constructor
    · intro hx
      rcases Submodule.mem_span_singleton.mp hx with ⟨c, rfl⟩
      simp [smul_apply]
    · intro hx
      rw [show x = x 1 • (![0, 1] : Fin 2 → ℚ) by
        funext i
        fin_cases i <;> simp [hx]]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have hker : ∀ x : Fin 2 → ℚ,
      x 0 + x 1 = 0 ↔ ∃ c : ℚ, x = c • ((![1, 0] : Fin 2 → ℚ) - ![0, 1]) := by
    intro x
    constructor
    · intro hx
      refine ⟨x 0, ?_⟩
      have hx' : x 1 = -x 0 := by linarith [hx]
      funext i
      fin_cases i <;> simp [smul_apply, hx']
    · rintro ⟨c, rfl⟩
      simp [smul_apply]
  repeat' constructor
  · exact hc1
  · exact hc2
  · intro x
    rw [hc1, hc2]
    constructor
    · intro h
      funext i
      fin_cases i <;> simp [h.1, h.2]
    · intro h
      subst h
      simp [hc1, hc2]
  · intro q
    refine ⟨q • (![1, 0] : Fin 2 → ℚ), ?_, ?_⟩
    · exact hc1 _ |>.2 (by simp)
    · simp [smul_apply]
  · intro q
    refine ⟨q • (![0, 1] : Fin 2 → ℚ), ?_, ?_⟩
    · exact hc2 _ |>.2 (by simp)
    · simp [smul_apply]
  · intro x hx hL
    rw [hc1] at hx
    have hx0 : x 0 = 0 := by linarith [hL, hx]
    funext i
    fin_cases i <;> simp [hx, hx0]
  · intro x hx hL
    rw [hc2] at hx
    have hx1 : x 1 = 0 := by linarith [hL, hx]
    funext i
    fin_cases i <;> simp [hx, hx1]
  · exact hker

end MathlibPlus.LinearAlgebra
