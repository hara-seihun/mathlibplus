import MathlibPlus.GroupTheory.TwoClosure

namespace MathlibPlus.GroupTheory.Claim28426

open MathlibPlus.GroupTheory.TwoClosure

/-- A transitive contained conjugate pair whose conjugator fixes the base point
and every base-point suborbit lies in the ambient 2-closure. -/
theorem suborbit_fixation_mem_twoClosure_claim28426
    {Ω : Type*} [Fintype Ω]
    (G H : Subgroup (Equiv.Perm Ω)) (q : Equiv.Perm Ω) (α : Ω)
    (_hGtrans : ∀ x y : Ω, ∃ g : Equiv.Perm Ω, g ∈ G ∧ g x = y)
    (hHtrans : ∀ x y : Ω, ∃ h : Equiv.Perm Ω, h ∈ H ∧ h x = y)
    (hHG : H ≤ G)
    (hconj : ∀ h : Equiv.Perm Ω, h ∈ H → q⁻¹ * h * q ∈ G)
    (hqa : q α = α)
    (horbit : ∀ x : Ω,
      q '' pointStabilizerOrbit G α x = pointStabilizerOrbit G α x) :
    inTwoClosure G q := by
  intro x y
  obtain ⟨h, hh, hqxa⟩ := hHtrans (q x) α
  let h' : Equiv.Perm Ω := q⁻¹ * h * q
  have hh' : h' ∈ G := hconj h hh
  have hqinvα : q⁻¹ α = α := by
    simpa using (congrArg (fun x : Ω => q⁻¹ x) hqa).symm
  have h'x : h' x = α := by
    change q⁻¹ (h (q x)) = α
    rw [hqxa, hqinvα]
  let z : Ω := h (q y)
  have h'y : h' y = q⁻¹ z := by
    change q⁻¹ (h (q y)) = q⁻¹ z
    rfl
  have hzO : z ∈ pointStabilizerOrbit G α z := by
    refine ⟨1, G.one_mem, ?_, ?_⟩ <;> simp
  have hzimg : z ∈ q '' pointStabilizerOrbit G α z := by
    rw [horbit z]
    exact hzO
  obtain ⟨w, hwO, hwq⟩ := hzimg
  have hw : w = q⁻¹ z := by
    apply q.injective
    simpa using hwq
  have hqinvzO : q⁻¹ z ∈ pointStabilizerOrbit G α z := by
    simpa [hw] using hwO
  obtain ⟨a, ha, haα, haz⟩ := hqinvzO
  have hainv : a⁻¹ ∈ G := G.inv_mem ha
  have hainvz : a⁻¹ (q⁻¹ z) = z := by
    rw [← haz]
    simp
  have h_inv_qx : h⁻¹ α = q x := by
    rw [← hqxa]
    simp
  have h_inv_z : h⁻¹ z = q y := by
    rw [show z = h (q y) by rfl]
    simp
  have hainvα : a⁻¹ α = α := by
    calc
      a⁻¹ α = a⁻¹ (a α) := by rw [haα]
      _ = α := by simp
  refine ⟨h⁻¹ * a⁻¹ * h', ?_, ?_, ?_⟩
  · exact G.mul_mem (G.mul_mem (G.inv_mem (hHG hh)) hainv) hh'
  · change h⁻¹ (a⁻¹ (h' x)) = q x
    rw [h'x, hainvα, h_inv_qx]
  · change h⁻¹ (a⁻¹ (h' y)) = q y
    rw [h'y, hainvz, h_inv_z]

end MathlibPlus.GroupTheory.Claim28426
