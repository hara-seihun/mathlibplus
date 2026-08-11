import MathlibPlus.Basic

namespace MathlibPlus.Algebra

/--
Claim 10425 in the concrete finite-dimensional matrix model: the determinant
of the trivial-parameter local factor on an `n`-dimensional complex space has
its inverse equal to the negative `n`th `zpow` of `1 - u`.
-/
theorem trivialParameterLocalFactor_claim10425 (n : ℕ) (u : ℂ) :
    (Matrix.det (1 - u • (1 : Matrix (Fin n) (Fin n) ℂ)))⁻¹ =
      (1 - u) ^ (-(n : ℤ)) := by
  have hmatrix :
      (1 : Matrix (Fin n) (Fin n) ℂ) - u • (1 : Matrix (Fin n) (Fin n) ℂ) =
        (1 - u) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · simp [h]
  rw [hmatrix, Matrix.det_smul, Matrix.det_one]
  rw [zpow_neg, zpow_natCast]
  simp [Fintype.card_fin]

end MathlibPlus.Algebra
