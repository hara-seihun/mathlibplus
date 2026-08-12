import Mathlib

namespace MathlibPlus.Algebra

/--
Formalization of admitted claim 8600.  The source's projective quantities are
anchored to the Cholesky coordinates: `q_n = r_n^2`,
`beta_n = r_(n-1) s_n`, and
`S_n = r_n^2 + s_n^2 - r_(n-1) s_n - r_n s_(n+1)`.
The nonzero hypotheses are precisely the local denominator conditions.
-/
theorem claim8600_projectiveRecurrence
    (r s : ℕ → ℝ) (k : ℕ) (hk : 0 < k)
    (hrprev : r (k - 1) ≠ 0) (hsprev : s k ≠ 0)
    (hr : r k ≠ 0) (hsnext : s (k + 1) ≠ 0) :
    let q : ℕ → ℝ := fun n => r n ^ 2
    let beta : ℕ → ℝ := fun n => r (n - 1) * s n
    let source : ℕ → ℝ := fun n =>
      r n ^ 2 + s n ^ 2 - r (n - 1) * s n - r n * s (n + 1)
    let d : ℕ → ℝ := fun n => q n / beta (n + 1) - 1
    let rho : ℕ → ℝ := fun n => beta n / beta (n + 1)
    let eps : ℕ → ℝ := fun n => source n / beta (n + 1)
    d k = rho k * d (k - 1) / (1 + d (k - 1)) + eps k := by
  dsimp
  have hkm : k - 1 + 1 = k := Nat.sub_add_cancel hk
  rw [hkm]
  field_simp [hrprev, hsprev, hr, hsnext]
  ring

end MathlibPlus.Algebra
