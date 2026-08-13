import Mathlib

namespace MathlibPlus.Analysis.Claim19598

open scoped InnerProductSpace

/-- The tree-level norm identity obtained from the adjointness relations and
`LG - GL = n I`.  The source's adjacent tree-level deck/grafting spaces are
represented by three arbitrary real inner-product spaces; `L` and `G` are the
lower-level pair, while `Lnext` and `Gnext` are the next-level pair. -/
theorem treeEnergyIdentity_claim19598
    {V W U : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (L : V →ₗ[ℝ] W) (G : W →ₗ[ℝ] V)
    (Lnext : U →ₗ[ℝ] V) (Gnext : V →ₗ[ℝ] U)
    (hLadj : ∀ x y, ⟪L x, y⟫_ℝ = ⟪x, G y⟫_ℝ)
    (hGadj : ∀ x y, ⟪Gnext x, y⟫_ℝ = ⟪x, Lnext y⟫_ℝ)
    (n : ℕ)
    (hcomm : Lnext ∘ₗ Gnext - G ∘ₗ L =
      (n : ℝ) • (LinearMap.id : V →ₗ[ℝ] V)) :
    ∀ x : V, ‖Gnext x‖ ^ 2 = ‖L x‖ ^ 2 + (n : ℝ) * ‖x‖ ^ 2 := by
  intro x
  have hcomm_x : Lnext (Gnext x) - G (L x) = (n : ℝ) • x := by
    have h := congrArg (fun T : V →ₗ[ℝ] V => T x) hcomm
    simpa [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply] using h
  have hadd : Lnext (Gnext x) = G (L x) + (n : ℝ) • x := by
    calc
      Lnext (Gnext x) =
          (Lnext (Gnext x) - G (L x)) + G (L x) := by abel
      _ = (n : ℝ) • x + G (L x) := by rw [hcomm_x]
      _ = G (L x) + (n : ℝ) • x := by abel
  calc
    ‖Gnext x‖ ^ 2 = ⟪Gnext x, Gnext x⟫_ℝ :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ⟪x, Lnext (Gnext x)⟫_ℝ := hGadj x (Gnext x)
    _ = ⟪x, G (L x) + (n : ℝ) • x⟫_ℝ := by rw [hadd]
    _ = ⟪x, G (L x)⟫_ℝ + (n : ℝ) * ⟪x, x⟫_ℝ := by
      rw [inner_add_right, real_inner_smul_right]
    _ = ‖L x‖ ^ 2 + (n : ℝ) * ‖x‖ ^ 2 := by
      rw [← hLadj x (L x), real_inner_self_eq_norm_sq,
        real_inner_self_eq_norm_sq]

end MathlibPlus.Analysis.Claim19598
