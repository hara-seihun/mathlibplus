import MathlibPlus.Algebra.ProjectiveStokes

namespace MathlibPlus.Algebra.ProjectiveStokes

/-- On the nonzero `X,D` chart, the zero of `X + D` is the projective
coordinate value `1` from claim 15385. -/
theorem zero_iff_projective_eq_one {ι K : Type*} [Field K]
    (X D : ι → K) (z : {z : ι // X z * D z ≠ 0}) :
    X z + D z = 0 ↔ projectiveStokesCoordinate X D z = 1 := by
  have hD : D z ≠ 0 := by
    intro h
    apply z.property
    simp [h]
  dsimp [projectiveStokesCoordinate]
  constructor
  · intro h
    apply (div_eq_iff hD).2
    simpa using (neg_eq_iff_add_eq_zero).2 h
  · intro h
    have h' := (div_eq_iff hD).1 h
    simp only [one_mul] at h'
    exact (neg_eq_iff_add_eq_zero).1 h'

/-- At a point where both summands are nonzero and differentiable, the
logarithmic derivative of `-X/D` is the difference of the logarithmic
 derivatives, as in claim 15385. -/
theorem projective_log_deriv_eq {X D : ℂ → ℂ} {z : ℂ}
    (hX : DifferentiableAt ℂ X z) (hD : DifferentiableAt ℂ D z)
    (hx : X z ≠ 0) (hd : D z ≠ 0) :
    deriv (fun w => -X w / D w) z / (-X z / D z) =
      deriv X z / X z - deriv D z / D z := by
  have hneg : HasDerivAt (fun w => -X w) (-deriv X z) z :=
    hX.hasDerivAt.neg
  have hquot := hneg.div hD.hasDerivAt hd
  have hderiv := hquot.deriv
  change deriv ((fun w => -X w) / D) z / (-X z / D z) = _
  rw [hderiv]
  field_simp [hx, hd]
  ring

end MathlibPlus.Algebra.ProjectiveStokes
