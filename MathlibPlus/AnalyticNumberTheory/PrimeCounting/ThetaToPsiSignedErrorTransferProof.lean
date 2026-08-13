import MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting.ThetaToPsiSignedErrorTransfer

namespace MathlibPlus.AnalyticNumberTheory.PrimeCounting

/-- The signed theta-to-psi error transfer follows from the pointwise order
of Chebyshev's theta and psi functions. -/
theorem thetaToPsiSignedErrorTransfer_proved :
    MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting.thetaToPsiSignedErrorTransfer := by
  constructor
  · intro x hx
    have hθψ : Chebyshev.theta x ≤ Chebyshev.psi x := Chebyshev.theta_le_psi x
    have hsub : Chebyshev.theta x - x ≤ Chebyshev.psi x - x := by linarith
    have hdiv : (Chebyshev.theta x - x) / x ≤
        (Chebyshev.psi x - x) / x :=
      (div_le_div_iff_of_pos_right hx).2 hsub
    exact ⟨hθψ, hdiv⟩
  · intro bound x hx hbound
    have hsub : Chebyshev.theta x - x ≤ Chebyshev.psi x - x := by
      linarith [Chebyshev.theta_le_psi x]
    have hdiv : (Chebyshev.theta x - x) / x ≤
        (Chebyshev.psi x - x) / x :=
      (div_le_div_iff_of_pos_right hx).2 hsub
    exact hdiv.trans hbound

end MathlibPlus.AnalyticNumberTheory.PrimeCounting
