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


/-- Claim 24477: the displayed factorization gives the equivalent cubic inequality. -/
theorem interiorSupportPolynomialInequality {y r : ℝ}
    (_hy0 : 0 < y) (hy4 : y < 4) (_hr0 : 0 < r) (_hr4 : r < 4) :
    (4 - y) * (y - r) ^ 2 ≥ 0 ∧
      ((4 - y) * (y - r) ^ 2 ≥ 0 ↔
        y ^ 3 ≤ 4 * r ^ 2 - (8 * r + r ^ 2) * y + (4 + 2 * r) * y ^ 2) := by
  have hnonneg : (4 - y) * (y - r) ^ 2 ≥ 0 :=
    mul_nonneg (by linarith) (sq_nonneg (y - r))
  have hfactor :
      (4 - y) * (y - r) ^ 2 =
        4 * r ^ 2 - (8 * r + r ^ 2) * y + (4 + 2 * r) * y ^ 2 - y ^ 3 := by
    ring
  refine ⟨hnonneg, ?_⟩
  rw [hfactor]
  constructor <;> intro h <;> linarith

/-- Claim 18092: squaring maps each positive integer cell onto the corresponding band. -/
theorem integerCell_square_image (n : ℕ) (hn : 0 < n) :
    (fun x : ℝ => x ^ 2) '' Set.Ioo (n : ℝ) (n + 1 : ℝ) =
      Set.Ioo ((n : ℝ) ^ 2) ((n + 1 : ℝ) ^ 2) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    constructor
    · have h₁ : 0 < x - (n : ℝ) := sub_pos.mpr hx.1
      have hn : 0 < (n : ℝ) := by exact_mod_cast hn
      have h₂ : 0 < x + (n : ℝ) := by linarith
      nlinarith [mul_pos h₁ h₂]
    · have h₁ : 0 < (n + 1 : ℝ) - x := sub_pos.mpr hx.2
      have hn : 0 < (n : ℝ) := by exact_mod_cast hn
      have hxpos : 0 < x := by linarith [hx.1]
      have h₂ : 0 < (n + 1 : ℝ) + x := by linarith
      nlinarith [mul_pos h₁ h₂]
  · intro hy
    have hy0 : 0 ≤ y := by
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      have hn_sq : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
      nlinarith [hy.1]
    let x : ℝ := Real.sqrt y
    have hx0 : 0 ≤ x := Real.sqrt_nonneg y
    have hx2 : x ^ 2 = y := by
      dsimp [x]
      exact Real.sq_sqrt hy0
    have hxn : (n : ℝ) < x := by
      by_contra h
      have hle : x ≤ (n : ℝ) := le_of_not_gt h
      have hprod : 0 ≤ ((n : ℝ) - x) * ((n : ℝ) + x) :=
        mul_nonneg (sub_nonneg.mpr hle) (by positivity)
      have hsquares : x ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith [hprod]
      nlinarith [hy.1, hx2, hsquares]
    have hxn1 : x < (n + 1 : ℝ) := by
      by_contra h
      have hle : (n + 1 : ℝ) ≤ x := le_of_not_gt h
      have hprod : 0 ≤ (x - (n + 1 : ℝ)) * (x + (n + 1 : ℝ)) :=
        mul_nonneg (sub_nonneg.mpr hle) (by positivity)
      have hsquares : x ^ 2 ≥ (n + 1 : ℝ) ^ 2 := by nlinarith [hprod]
      nlinarith [hy.2, hx2, hsquares]
    exact ⟨x, ⟨hxn, hxn1⟩, hx2⟩

end MathlibPlus.Algebra.Identities
