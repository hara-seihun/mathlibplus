import Mathlib

namespace MathlibPlus.Algebra.Claim5349

/-- The two displayed rational Hilbert-series contributions combine to the
candidate path series away from the pole at `t = 1`. -/
theorem hilbertSeriesAlgebra_claim5349 (t : ℚ) (ht : 1 - t ≠ 0) :
    (1 + t) / (1 - t) ^ 3 + 2 / (1 - t) ^ 2 =
      (3 - t) / (1 - t) ^ 3 := by
  field_simp [ht]
  ring

end MathlibPlus.Algebra.Claim5349

namespace MathlibPlus.Algebra.Claim7277

/-- A linear first-slot Bezout pencil has the displayed translation identity.
The derivative is unchanged by subtracting the scalar polynomial `C ε`. -/
theorem derivativeBezoutPencil_claim7277 {R : Type*} [CommRing R]
    (B : Polynomial R →ₗ[R] Polynomial R →ₗ[R] Polynomial R)
    (P : Polynomial R) (ε : R) :
    B P P.derivative - ε • B 1 P.derivative =
      B (P - Polynomial.C ε) P.derivative := by
  have hC : Polynomial.C ε = ε • (1 : Polynomial R) := by
    ext n
    cases n with
    | zero => simp [Polynomial.coeff_one]
    | succ n => simp [Polynomial.coeff_one]
  rw [map_sub, hC, map_smul]
  rfl

end MathlibPlus.Algebra.Claim7277

namespace MathlibPlus.Algebra.Claim8604

/-- The projective ratio is the diagonal-to-subdiagonal ratio when the
continuant numerator is the square of the diagonal entry. -/
theorem projectiveJacobiRatio_claim8604 {K : Type*} [Field K]
    (r s q β : K) (hr : r ≠ 0) (hs : s ≠ 0)
    (hq : q = r ^ 2) (hβ : β = r * s) :
    q / β = r / s := by
  rw [hq, hβ]
  field_simp [hr, hs]

end MathlibPlus.Algebra.Claim8604

namespace MathlibPlus.Combinatorics.Claim21057

/-- The exact-three lower bound on `t` gives the displayed lower bound on the
odd family cardinality. -/
theorem exactThreeCardinalityLowerBound_claim21057
    {N t familyCard : ℕ} (ht : 2 * N + 7 ≤ t)
    (hcard : familyCard = 2 * t + 1) :
    4 * N + 15 ≤ familyCard := by
  omega

end MathlibPlus.Combinatorics.Claim21057

namespace MathlibPlus.Combinatorics.Claim50537

/-- The two exact sign rows have positive-coordinate masks `85` and `195`.
The mask convention is made explicit rather than hidden in notation. -/
theorem truthTableRows_claim50537 :
    let h : Fin 8 → ℚ := ![1, -1, 1, -1, 1, -1, 1, -1]
    let k : Fin 8 → ℚ := ![1, 1, -1, -1, -1, -1, 1, 1]
    let mask : (Fin 8 → ℚ) → ℕ :=
      fun v => ∑ i : Fin 8, if v i = 1 then 2 ^ i.1 else 0
    mask h = 85 ∧ mask k = 195 := by
  dsimp
  constructor <;> norm_num [Fin.sum_univ_succ]

/-- The rational mixture of the two displayed sign rows has the exact
coordinate values shown below. -/
theorem truthTableMixture_claim50537 (t : ℚ) :
    let h : Fin 8 → ℚ := ![1, -1, 1, -1, 1, -1, 1, -1]
    let k : Fin 8 → ℚ := ![1, 1, -1, -1, -1, -1, 1, 1]
    let u : Fin 8 → ℚ := fun i => t * h i + (1 - t) * k i
    u = ![1, 1 - 2 * t, 2 * t - 1, -1,
      2 * t - 1, -1, 1, 1 - 2 * t] := by
  dsimp
  funext i
  fin_cases i <;> simp <;> ring

end MathlibPlus.Combinatorics.Claim50537

namespace MathlibPlus.Analysis.Claim15752

/-- The displayed primitive rank-four coefficient is strictly negative. -/
theorem primitiveRankFourCoefficient_negative_claim15752 (c : ℚ)
    (hc : c = -3901 / 16777216) : c < 0 := by
  rw [hc]
  norm_num

end MathlibPlus.Analysis.Claim15752

namespace MathlibPlus.Combinatorics.Claim50537

/-- A convex mixture of the two displayed sign rows remains coordinatewise in
`[-1,1]` when its rational weight lies in `[0,1]`. -/
theorem truthTableMixtureBounds_claim50537 (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let h : Fin 8 → ℚ := ![1, -1, 1, -1, 1, -1, 1, -1]
    let k : Fin 8 → ℚ := ![1, 1, -1, -1, -1, -1, 1, 1]
    let u : Fin 8 → ℚ := fun i => t * h i + (1 - t) * k i
    ∀ i : Fin 8, (-1 : ℚ) ≤ u i ∧ u i ≤ 1 := by
  dsimp
  intro i
  fin_cases i <;> simp <;> (first | (constructor <;> linarith) | linarith)

end MathlibPlus.Combinatorics.Claim50537
