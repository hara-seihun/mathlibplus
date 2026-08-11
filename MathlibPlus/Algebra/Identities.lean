import Mathlib

/-!
# Elementary algebraic identities

Formalizations of admitted claims 4188, 11262, and 18273.
-/

namespace MathlibPlus.Algebra.Identities

/--
Claim 4188, with the forward differences expanded:
`Δ S n = S (n+1) - S n` and
`Δ² S n = S (n+2) - 2*S (n+1) + S n`.

The source does not specify the scalar domain; the identity is algebraic and is
therefore stated for an arbitrary commutative ring.
-/
theorem forwardDifferenceTuranIdentity {R : Type*} [CommRing R]
    (S : ℕ → R) (n : ℕ) :
    S n * (S (n + 2) - 2 * S (n + 1) + S n) -
        (S (n + 1) - S n) ^ 2 =
      S n * S (n + 2) - (S (n + 1)) ^ 2 := by
  ring

/--
Claim 11262's completed-cell rising-Pochhammer identity.  The source's
`(α)_p` is represented by Mathlib's `ascPochhammer ℝ p` evaluated at `α`.
-/
theorem completedCellPochhammerDifference (α : ℝ) {p : ℕ} (hp : 1 ≤ p) :
    (ascPochhammer ℝ p).eval (α + 1) - (ascPochhammer ℝ p).eval α =
      (p : ℝ) * (ascPochhammer ℝ (p - 1)).eval (α + 1) := by
  cases p with
  | zero => omega
  | succ q =>
    simp only [Nat.succ_sub_one]
    have h := congrArg (fun r : Polynomial ℝ => r.eval α)
      (ascPochhammer_succ_comp_X_add_one (S := ℝ) q)
    have h' :
        (ascPochhammer ℝ (q + 1)).eval (α + 1) =
          (ascPochhammer ℝ (q + 1)).eval α +
            (q + 1 : ℝ) * (ascPochhammer ℝ q).eval (α + 1) := by
      simpa [Polynomial.eval_comp] using h
    norm_num [Nat.cast_add, Nat.cast_one] at h' ⊢
    linarith

/-- Positivity of the right side in claim 11262 under `α > 0` and `p ≥ 1`. -/
theorem completedCellPochhammerDifference_pos (α : ℝ) {p : ℕ}
    (hα : 0 < α) (hp : 1 ≤ p) :
    0 < (p : ℝ) * (ascPochhammer ℝ (p - 1)).eval (α + 1) := by
  exact mul_pos (by exact_mod_cast hp)
    (ascPochhammer_pos (p - 1) (α + 1) (by linarith))

/--
Claim 18273's exact unaugmented connectivity identity.  The source defines
`Z(w) = S + (2*w - 1)*T` and `δ(w) = w - 1`; those expressions are kept
inline here so no additional definitions are introduced.
-/
theorem unaugmentedConnectivityIdentity {R : Type*} [CommRing R]
    (S T w : R) :
    w * S + w * T =
      (S + (2 * w - 1) * T) + (w - 1) * (S - T) := by
  ring

end MathlibPlus.Algebra.Identities
