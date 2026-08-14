import Mathlib

namespace MathlibPlus.Open.NewResearch2.BlowupTangent

noncomputable section

/-- Claim 18635: the scaled curve has the displayed limiting tangent curve.
The original curve is kept as a function-valued carrier so that the scaling
`q = Q / t` and the limiting operation are both part of the statement. -/
def claim18635_parabolicWallBlowupTangentCurve
    (gamma : ℝ → ℝ → (Fin 3 → ℝ))
    (v : ℝ → (Fin 3 → ℝ)) : Prop :=
  (∀ Q : ℝ,
    Filter.Tendsto (fun t : ℝ => gamma (Q / t) t)
      (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds (v Q))) ∧
    (∀ Q : ℝ,
      v Q (0 : Fin 3) = Real.tanh Q + Q * (Real.cosh Q)⁻¹ ^ 2 ∧
      v Q (1 : Fin 3) = 2 * Q ∧
      v Q (2 : Fin 3) =
        Q ^ 2 * (3 * Real.tanh Q + Q * (Real.cosh Q)⁻¹ ^ 2))

/-- Claim 18640: a positive even-series certificate gives the required signs.
The final factor is explicitly the square of the named radius function. -/
def claim18640_positiveThirdWronskianNumerator
    (N r W : ℝ → ℝ) (a : ℕ → ℝ) : Prop :=
  ((∀ n : ℕ, 0 ≤ a n) ∧
    (∃ n : ℕ, 0 < a n) ∧
    (∀ Q : ℝ, 0 < Q →
      HasSum (fun n : ℕ => a n * Q ^ (2 * n)) (N Q)) ∧
    (∀ Q : ℝ, 0 < Q → 0 < r Q ^ 2) ∧
    (∀ Q : ℝ, W Q = N Q * r Q ^ 2)) →
    (∀ Q : ℝ, 0 < Q → 0 < N Q ∧ 0 < W Q)

/-- Claim 18641: the three coordinate functions form a strict ECT system on
`(0,∞)`, expressed by nonvanishing initial confluent Wronskians. -/
def claim18641_strictExtendedCompleteChebyshev
    (v : ℝ → (Fin 3 → ℝ)) : Prop :=
  ∀ m : Fin 3, ∀ x : ℝ, 0 < x →
    Matrix.det
      (fun i j : Fin (m.val + 1) =>
        iteratedDeriv j.val
          (fun z : ℝ => v z (Fin.castLE (Nat.succ_le_of_lt m.isLt) i)) x) ≠ 0

/-- Claim 18642: every ordered positive three-point evaluation determinant is
strictly positive. -/
def claim18642_orderedThreePointDeterminantPositivity
    (v : ℝ → (Fin 3 → ℝ)) : Prop :=
  ∀ q : Fin 3 → ℝ,
    0 < q (0 : Fin 3) ∧
      q (0 : Fin 3) < q (1 : Fin 3) ∧
      q (1 : Fin 3) < q (2 : Fin 3) →
    Matrix.det (fun i j : Fin 3 => v (q i) j) > 0

end
end MathlibPlus.Open.NewResearch2.BlowupTangent
