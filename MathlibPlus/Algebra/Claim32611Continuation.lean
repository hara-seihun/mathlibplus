import Mathlib

namespace MathlibPlus.Algebra.Claim32611

/--
The exact five-term singleton-continuation polynomial from claim 32611 is
nonzero, has the displayed factor `x₁`, and vanishes after setting `x₁ = 0`.
The source-specific full-signature construction is intentionally not
reconstructed here; these are the explicit polynomial consequences recorded in
the claim.
-/
theorem singletonContinuationCore_claim32611 :
    let F : MvPolynomial (Fin 4) ℤ :=
      (MvPolynomial.X 0) ^ 3 * MvPolynomial.X 3 -
          2 * (MvPolynomial.X 0) ^ 2 * MvPolynomial.X 1 * MvPolynomial.X 2 +
        MvPolynomial.X 0 * (MvPolynomial.X 1) ^ 3 +
          MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 3 -
        MvPolynomial.X 0 * (MvPolynomial.X 2) ^ 2
    F ≠ 0 ∧
      (∃ P : MvPolynomial (Fin 4) ℤ, F = MvPolynomial.X 0 * P) ∧
      ∀ x : Fin 4 → ℤ,
        MvPolynomial.eval (Function.update x 0 0) F = 0 := by
  dsimp
  let F : MvPolynomial (Fin 4) ℤ :=
      (MvPolynomial.X 0) ^ 3 * MvPolynomial.X 3 -
          2 * (MvPolynomial.X 0) ^ 2 * MvPolynomial.X 1 * MvPolynomial.X 2 +
        MvPolynomial.X 0 * (MvPolynomial.X 1) ^ 3 +
          MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 3 -
        MvPolynomial.X 0 * (MvPolynomial.X 2) ^ 2
  change F ≠ 0 ∧
      (∃ P : MvPolynomial (Fin 4) ℤ, F = MvPolynomial.X 0 * P) ∧
      ∀ x : Fin 4 → ℤ,
        MvPolynomial.eval (Function.update x 0 0) F = 0
  constructor
  · intro h
    have hv := congrArg
      (MvPolynomial.eval (![1, 0, 0, 1] : Fin 4 → ℤ)) h
    have h₃ : (![1, 0, 0, 1] : Fin 4 → ℤ) 3 = 1 := by rfl
    have h₂ : (![1, 0, 0, 1] : Fin 4 → ℤ) 2 = 0 := by rfl
    norm_num [F, h₃, h₂] at hv
  constructor
  · refine ⟨(MvPolynomial.X 0) ^ 2 * MvPolynomial.X 3 -
          2 * MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 +
        (MvPolynomial.X 1) ^ 3 + MvPolynomial.X 1 * MvPolynomial.X 3 -
          (MvPolynomial.X 2) ^ 2, ?_⟩
    change
      (MvPolynomial.X 0) ^ 3 * MvPolynomial.X 3 -
          2 * (MvPolynomial.X 0) ^ 2 * MvPolynomial.X 1 * MvPolynomial.X 2 +
        MvPolynomial.X 0 * (MvPolynomial.X 1) ^ 3 +
          MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 3 -
        MvPolynomial.X 0 * (MvPolynomial.X 2) ^ 2 =
      MvPolynomial.X 0 * ((MvPolynomial.X 0) ^ 2 * MvPolynomial.X 3 -
          2 * MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 +
        (MvPolynomial.X 1) ^ 3 + MvPolynomial.X 1 * MvPolynomial.X 3 -
          (MvPolynomial.X 2) ^ 2)
    ring
  · intro x
    simp [F, MvPolynomial.eval, Function.update_self]

end MathlibPlus.Algebra.Claim32611
