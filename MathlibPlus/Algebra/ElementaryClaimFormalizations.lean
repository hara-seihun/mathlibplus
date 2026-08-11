import MathlibPlus.Basic

namespace MathlibPlus.Algebra.SplitPositiveQuadratics

/-!
Formalization of admitted claim 24577.  The source does not fix a coefficient
field, so the algebraic identity is stated over an arbitrary strictly ordered
commutative ring; `t` and the positive value `Y` range over that ring.
-/

/-- The three displayed positive quadratics have the stated common root sum,
product relation, and affine dependence. -/
theorem splitPositiveQuadratics
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (Y : R) (hY : 0 < Y) :
    let C₀ : R → R := fun t => (t - 7 * Y) * (t - 9 * Y)
    let C₁ : R → R := fun t => (t - 3 * Y) * (t - 13 * Y)
    let C₂ : R → R := fun t => (t - Y) * (t - 15 * Y)
    0 < 7 * Y ∧ 0 < 9 * Y ∧ 0 < 3 * Y ∧ 0 < 13 * Y ∧
      0 < Y ∧ 0 < 15 * Y ∧
      7 * Y + 9 * Y = 16 * Y ∧
      3 * Y + 13 * Y = 16 * Y ∧
      Y + 15 * Y = 16 * Y ∧
      63 * Y ^ 2 - 2 * (39 * Y ^ 2) + 15 * Y ^ 2 = 0 ∧
      ∀ t : R, C₀ t - 2 * C₁ t + C₂ t = 0 := by
  dsimp
  have h7 : (0 : R) < 7 := by norm_num
  have h9 : (0 : R) < 9 := by norm_num
  have h3 : (0 : R) < 3 := by norm_num
  have h13 : (0 : R) < 13 := by norm_num
  have h15 : (0 : R) < 15 := by norm_num
  refine ⟨mul_pos h7 hY, mul_pos h9 hY, mul_pos h3 hY, mul_pos h13 hY,
    hY, mul_pos h15 hY, ?_, ?_, ?_, ?_, ?_⟩
  · ring
  · ring
  · ring
  · ring
  · intro t
    ring

end MathlibPlus.Algebra.SplitPositiveQuadratics

namespace MathlibPlus.LinearAlgebra.CompanionFrobenius

/-!
Formalization of admitted claim 11105.  The integer matrices are extended
coefficientwise to `Polynomial ℤ` before forming `I - T Fᵢ`.
-/

/-- The two displayed companion matrices realize the two displayed
characteristic-series polynomials. -/
theorem companionFrobeniusMatrices :
    let T : Polynomial ℤ := Polynomial.X
    let F₁ : Matrix (Fin 2) (Fin 2) ℤ := !![0, -5; 1, -3]
    let F₂ : Matrix (Fin 2) (Fin 2) ℤ := !![0, -5; 1, 4]
    Matrix.det (1 - T • (F₁.map Polynomial.C)) = 1 + 3 * T + 5 * T ^ 2 ∧
      Matrix.det (1 - T • (F₂.map Polynomial.C)) = 1 - 4 * T + 5 * T ^ 2 := by
  dsimp
  constructor <;>
    rw [Matrix.det_fin_two] <;>
    simp [Matrix.smul_apply] <;>
    ring

end MathlibPlus.LinearAlgebra.CompanionFrobenius

namespace MathlibPlus.Algebra

/-!
Formalization of admitted claim 24957.  The four-term minimum is written with
nested `min`s, preserving all four cross-sums in the source statement.
-/

/-- The cross-minimum identity for four nonnegative integer valuations. -/
theorem crossMinimumIdentity (x y u v : ℕ) :
    min (min (x + u) (y + v)) (min (x + v) (y + u)) =
      min x y + min u v := by
  omega

/-!
Formalization of admitted claim 19050.  The real parameters are coerced to
`ℂ`, and the source's complex exponential and hyperbolic cosine are retained.
-/

/-- A reflected pair of exponentials has the displayed hyperbolic-cosine form. -/
theorem reflectedFactorIdentity (a r : ℝ) (z : ℂ) :
    (1 + (r : ℂ) * Complex.exp ((a : ℂ) * z)) *
        (1 + (r : ℂ) * Complex.exp (-((a : ℂ) * z))) =
      1 + (r : ℂ) ^ 2 + 2 * (r : ℂ) * Complex.cosh ((a : ℂ) * z) := by
  simp only [Complex.cosh]
  have hexp : Complex.exp ((a : ℂ) * z) * Complex.exp (-((a : ℂ) * z)) = 1 := by
    rw [← Complex.exp_add]
    simp
  calc
    (1 + (r : ℂ) * Complex.exp ((a : ℂ) * z)) *
          (1 + (r : ℂ) * Complex.exp (-((a : ℂ) * z))) =
        1 + (r : ℂ) * Complex.exp ((a : ℂ) * z) +
          (r : ℂ) * Complex.exp (-((a : ℂ) * z)) +
          (r : ℂ) ^ 2 *
            (Complex.exp ((a : ℂ) * z) * Complex.exp (-((a : ℂ) * z))) := by ring
    _ = 1 + (r : ℂ) ^ 2 + 2 * (r : ℂ) *
          ((Complex.exp ((a : ℂ) * z) + Complex.exp (-((a : ℂ) * z))) / 2) := by
      rw [hexp]
      ring

end MathlibPlus.Algebra
