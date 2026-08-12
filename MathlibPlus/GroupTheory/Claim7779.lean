import Mathlib

namespace MathlibPlus.GroupTheory.Claim7779

/--
The scalar projective cocycle calculation from admitted claim 7779.  The
operators act on an arbitrary complex module; the involution equations and
the displayed projective commutation relation are the only operator
hypotheses used for the algebraic conclusions.  The unitary assumptions in
the source are therefore not silently encoded as extra analytic structure.
-/
theorem projective_product_square
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (U_h U_c : E →ₗ[ℂ] E) (ω : ℂ)
    (hh : U_h.comp U_h = LinearMap.id)
    (hc : U_c.comp U_c = LinearMap.id)
    (hrel : U_h.comp U_c = ω • (U_c.comp U_h)) :
    (U_h.comp U_c).comp (U_h.comp U_c) = ω • LinearMap.id := by
  apply LinearMap.ext
  intro x
  have hh_apply (y : E) : U_h (U_h y) = y := by
    have h := congrArg (fun f => f y) hh
    simpa [LinearMap.comp_apply] using h
  have hc_apply (y : E) : U_c (U_c y) = y := by
    have h := congrArg (fun f => f y) hc
    simpa [LinearMap.comp_apply] using h
  have hrel_apply (y : E) :
      U_h (U_c y) = ω • U_c (U_h y) := by
    have h := congrArg (fun f => f y) hrel
    simpa [LinearMap.comp_apply, LinearMap.smul_apply] using h
  change U_h (U_c (U_h (U_c x))) = ω • x
  calc
    U_h (U_c (U_h (U_c x))) =
        ω • U_c (U_h (U_h (U_c x))) := hrel_apply _
    _ = ω • U_c (U_c x) := by rw [hh_apply]
    _ = ω • x := by rw [hc_apply]

/-- Involutive projective commutation forces the scalar to be a sign. -/
theorem projective_cocycle_scalar_is_sign
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    [NoZeroSMulDivisors ℂ E] [Nontrivial E]
    (U_h U_c : E →ₗ[ℂ] E) (ω : ℂ)
    (hh : U_h.comp U_h = LinearMap.id)
    (hc : U_c.comp U_c = LinearMap.id)
    (hrel : U_h.comp U_c = ω • (U_c.comp U_h)) :
    ω = 1 ∨ ω = -1 := by
  let P := U_h.comp U_c
  let Q := U_c.comp U_h
  have hh_apply (x : E) : U_h (U_h x) = x := by
    have h := congrArg (fun f => f x) hh
    simpa [LinearMap.comp_apply] using h
  have hc_apply (x : E) : U_c (U_c x) = x := by
    have h := congrArg (fun f => f x) hc
    simpa [LinearMap.comp_apply] using h
  have hrel_apply (x : E) :
      U_h (U_c x) = ω • U_c (U_h x) := by
    have h := congrArg (fun f => f x) hrel
    simpa [LinearMap.comp_apply, LinearMap.smul_apply] using h
  have hPQ_apply (x : E) : P (Q x) = x := by
    change U_h (U_c (U_c (U_h x))) = x
    rw [hc_apply, hh_apply]
  have hQP_apply (x : E) : Q (P x) = x := by
    change U_c (U_h (U_h (U_c x))) = x
    rw [hh_apply, hc_apply]
  have hP2_apply (x : E) : P (P x) = ω • x := by
    change U_h (U_c (U_h (U_c x))) = ω • x
    calc
      U_h (U_c (U_h (U_c x))) =
          ω • U_c (U_h (U_h (U_c x))) := hrel_apply _
      _ = ω • U_c (U_c x) := by rw [hh_apply]
      _ = ω • x := by rw [hc_apply]
  have hQ2_apply (x : E) : Q (Q x) = ω • x := by
    change U_c (U_h (U_c (U_h x))) = ω • x
    calc
      U_c (U_h (U_c (U_h x))) =
          U_c (ω • U_c (U_h (U_h x))) := by rw [hrel_apply]
      _ = ω • U_c (U_c (U_h (U_h x))) := by simp
      _ = ω • x := by rw [hh_apply, hc_apply]
  have hfour (x : E) : P (P (Q (Q x))) = x := by
    rw [hPQ_apply, hPQ_apply]
  obtain ⟨e, he⟩ := exists_ne (0 : E)
  have homega : ω • (ω • e) = e := by
    calc
      ω • (ω • e) = ω • (Q (Q e)) := by rw [hQ2_apply]
      _ = P (P (Q (Q e))) := by rw [hP2_apply]
      _ = e := hfour _
  have hs : ω ^ 2 • e = e := by
    simpa [smul_smul, pow_two] using homega
  have hz : (ω ^ 2 - 1) • e = 0 := by
    rw [sub_smul, hs]
    simp
  rcases (noZeroSMulDivisors_iff ℂ E).mp
      (inferInstance : NoZeroSMulDivisors ℂ E) hz with hω | he0
  · exact (sq_eq_one_iff).mp (sub_eq_zero.mp hω)
  · exact (he he0).elim

/-- A nonzero vector fixed by the projective product forces the commuting sign. -/
theorem paired_fixed_vector_forces_one
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    [NoZeroSMulDivisors ℂ E] [Nontrivial E]
    (U_h U_c : E →ₗ[ℂ] E) (ω : ℂ)
    (hh : U_h.comp U_h = LinearMap.id)
    (hc : U_c.comp U_c = LinearMap.id)
    (hrel : U_h.comp U_c = ω • (U_c.comp U_h))
    {v : E} (hv : v ≠ 0)
    (hfixed : (U_h.comp U_c) v = v) :
    ω = 1 := by
  have hsquare := projective_product_square U_h U_c ω hh hc hrel
  have hfix : ω • v = v := by
    have h := congrArg (fun f => f v) hsquare
    simpa [LinearMap.comp_apply, LinearMap.smul_apply, hfixed] using h.symm
  have hz : (ω - 1) • v = 0 := by
    rw [sub_smul, hfix]
    simp
  rcases (noZeroSMulDivisors_iff ℂ E).mp
      (inferInstance : NoZeroSMulDivisors ℂ E) hz with hω | hv0
  · exact sub_eq_zero.mp hω
  · exact (hv hv0).elim

/-- The anticommuting sign has no nonzero fixed paired vector. -/
theorem anticommuting_has_no_nonzero_paired_vector
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    [NoZeroSMulDivisors ℂ E] [Nontrivial E]
    (U_h U_c : E →ₗ[ℂ] E) (ω : ℂ)
    (hh : U_h.comp U_h = LinearMap.id)
    (hc : U_c.comp U_c = LinearMap.id)
    (hrel : U_h.comp U_c = ω • (U_c.comp U_h))
    (hanti : ω = -1) :
    ¬ ∃ v : E, v ≠ 0 ∧ (U_h.comp U_c) v = v := by
  rintro ⟨v, hv, hfixed⟩
  have hone := paired_fixed_vector_forces_one U_h U_c ω hh hc hrel hv hfixed
  rw [hone] at hanti
  norm_num at hanti

end MathlibPlus.GroupTheory.Claim7779
