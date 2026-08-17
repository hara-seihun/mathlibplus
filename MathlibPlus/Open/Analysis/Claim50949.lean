import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.Claim50949

/-- The positive ordered analytic reserve setup with the canonical rank-four
shell scalar reproduction identity. -/
def positiveConnectedReserveSetup
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [PartialOrder P] [IsOrderedAddMonoid P]
    (R : ℝ × ℝ → P) (ell : P →ₗ[ℝ] ℝ)
    (R_a R_b R_ab : P) (a b : ℝ) : Prop :=
  AnalyticAt ℝ R ((0, 0) : ℝ × ℝ) ∧
    (∀ x : P, 0 ≤ x → 0 ≤ ell x) ∧
    0 ≤ R_ab ∧
    Asymptotics.IsBigO (nhds ((0, 0) : ℝ × ℝ))
      (fun z : ℝ × ℝ =>
        R z - (z.1 • R_a + z.2 • R_b + (z.1 * z.2) • R_ab))
      (fun z : ℝ × ℝ => z.1 ^ 2 + z.2 ^ 2) ∧
    ell (R (a, b)) =
      let m : ℕ → ℝ := fun j =>
        1 + (a / Real.sqrt 2) * ((4 : ℝ)⁻¹ ^ j) +
          (b / Real.sqrt 3) * ((9 : ℝ)⁻¹ ^ j)
      let h : ℕ → ℝ := fun j => m j / (Nat.factorial (2 * j) : ℝ)
      let delta : ℝ := Matrix.det (fun i j : Fin 4 =>
        ∑ q ∈ Finset.range (Nat.min i.val j.val + 1),
          ((i.val + j.val + 1 - 2 * q : ℕ) : ℝ) *
            h q * h (i.val + j.val + 1 - q))
      let delta₀ : ℝ := Matrix.det (fun i j : Fin 4 =>
        ∑ q ∈ Finset.range (Nat.min i.val j.val + 1),
          ((i.val + j.val + 1 - 2 * q : ℕ) : ℝ) *
            (1 / (Nat.factorial (2 * q) : ℝ)) *
            (1 / (Nat.factorial (2 * (i.val + j.val + 1 - q)) : ℝ)))
      Real.log (delta / delta₀)

end MathlibPlus.Open.Analysis.Claim50949
