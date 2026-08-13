import MathlibPlus.Basic

open scoped ENNReal

namespace MathlibPlus.Analysis.Claim9634

/-- An orthogonal (linear-isometric) change of coordinates preserves the
successive-minimum radius set, hence every successive minimum. The carrier
`L` is intentionally arbitrary: a lattice is a special case. -/
theorem successiveMinimum_orthogonalInvariant_claim9634
    {V W : Type*} [SeminormedAddCommGroup V] [SeminormedAddCommGroup W]
    [NormedSpace ℝ V] [NormedSpace ℝ W]
    (e : V ≃ₗᵢ[ℝ] W) (L : Set V) (k : ℕ) :
    let admissibleV : ℝ≥0∞ → Prop := fun r =>
      ∃ v : Fin k → V,
        (∀ i, v i ∈ L) ∧
          LinearIndependent ℝ v ∧
            ∀ i, ENNReal.ofReal ‖v i‖ ≤ r
    let admissibleW : ℝ≥0∞ → Prop := fun r =>
      ∃ w : Fin k → W,
        (∀ i, w i ∈ e '' L) ∧
          LinearIndependent ℝ w ∧
            ∀ i, ENNReal.ofReal ‖w i‖ ≤ r
    sInf {r | admissibleV r} = sInf {r | admissibleW r} := by
  dsimp
  apply congrArg sInf
  ext r
  constructor
  · rintro ⟨v, hv, hli, hbound⟩
    refine ⟨fun i => e (v i), ?_, ?_, ?_⟩
    · intro i
      exact ⟨v i, hv i, rfl⟩
    · simpa [Function.comp_def] using
        hli.map' e.toLinearEquiv.toLinearMap e.toLinearEquiv.ker
    · intro i
      simpa [e.norm_map] using hbound i
  · rintro ⟨w, hw, hli, hbound⟩
    let v : Fin k → V := fun i => e.symm (w i)
    have hv : ∀ i, v i ∈ L := by
      intro i
      rcases hw i with ⟨x, hx, hxe⟩
      have hev : v i = x := by
        dsimp [v]
        rw [← hxe]
        simp
      simpa [hev] using hx
    refine ⟨v, hv, ?_, ?_⟩
    · simpa [v, Function.comp_def] using
        hli.map' e.symm.toLinearEquiv.toLinearMap e.symm.toLinearEquiv.ker
    · intro i
      simpa [v, e.symm.norm_map] using hbound i

end MathlibPlus.Analysis.Claim9634
