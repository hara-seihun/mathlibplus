import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.CellwiseTransport

noncomputable section

/-- The two-exponential kernel used by the cellwise transport claims. -/
def claim48439_cellwiseTaylor : Prop :=
  let H : ℝ → ℝ → ℝ → ℝ := fun b q t =>
    Real.exp (-b * t - q * Real.exp (-t)) +
      Real.exp (b * t - q * Real.exp t)
  ∀ (n : ℕ) (x t : ℝ),
    (n : ℝ) < x → x < (n : ℝ) + 1 →
      let a : ℝ := 5 / 4
      let Q : ℝ := Real.pi * ((n : ℝ) + 1) ^ 2
      let s : ℝ := Q - Real.pi * x ^ 2
      H a (Q - s) t =
          ∑' k : ℕ,
            (s ^ k / (Nat.factorial k : ℝ)) * H (a + k) Q t ∧
        ∀ k : ℕ, 0 < s ^ k / (Nat.factorial k : ℝ)

/-- Exact heterogeneous-rank cellwise Taylor transport, with the cell and
point coordinates retained rather than replaced by an unconstrained matrix. -/
def claim48440_heterogeneousDeterminantTransport : Prop :=
  let H : ℝ → ℝ → ℝ → ℝ := fun b q t =>
    Real.exp (-b * t - q * Real.exp (-t)) +
      Real.exp (b * t - q * Real.exp t)
  ∀ (r : ℕ) (cell : Fin r → ℕ) (x t : Fin r → ℝ),
    (∀ i, (cell i : ℝ) < x i ∧ x i < (cell i : ℝ) + 1) →
    (∀ i j, i ≠ j → cell i ≠ cell j) →
    (∀ i j, i.1 < j.1 → t i < t j) →
    let a : ℝ := 5 / 4
    let Q : Fin r → ℝ := fun i =>
      Real.pi * ((cell i : ℝ) + 1) ^ 2
    let s : Fin r → ℝ := fun i =>
      Q i - Real.pi * (x i) ^ 2
    Matrix.det (fun i j => H a (Q i - s i) (t j)) =
      ∑' K : Fin r → ℕ,
        (∏ i : Fin r, s i ^ K i / (Nat.factorial (K i) : ℝ)) *
          Matrix.det (fun i j => H (a + K i) (Q i) (t j))

/-- The displayed rank-two wall minor is strictly negative at the given
integer cell indices, shifts, and ordered real wall parameters. -/
def claim48441_negativeWallMinor : Prop :=
  let H : ℝ → ℝ → ℝ → ℝ := fun b q t =>
    Real.exp (-b * t - q * Real.exp (-t)) +
      Real.exp (b * t - q * Real.exp t)
  let a : ℝ := 5 / 4
  let m : Fin 2 → ℕ := ![2, 5]
  let k : Fin 2 → ℕ := ![5, 11]
  let t : Fin 2 → ℝ :=
    ![(24023765826260427 : ℝ) / 10000000000000000,
      (279690777001533 : ℝ) / 100000000000000]
  Matrix.det (fun i j =>
    H (a + (k i : ℝ)) (Real.pi * (m i : ℝ) ^ 2) (t j)) < 0

/-- The original point minor remains strictly positive at the two specified
points, whose square-root coordinates lie in cells `(1,2)` and `(4,5)`. -/
def claim48442_positivePointMinor : Prop :=
  let H : ℝ → ℝ → ℝ → ℝ := fun b q t =>
    Real.exp (-b * t - q * Real.exp (-t)) +
      Real.exp (b * t - q * Real.exp t)
  let a : ℝ := 5 / 4
  let q : Fin 2 → ℝ := ![4 * Real.pi - 1, 25 * Real.pi - 1]
  let t : Fin 2 → ℝ :=
    ![(24023765826260427 : ℝ) / 10000000000000000,
      (279690777001533 : ℝ) / 100000000000000]
  (∃ y : Fin 2 → ℝ,
      1 < y 0 ∧ y 0 < 2 ∧ q 0 = Real.pi * (y 0) ^ 2 ∧
      4 < y 1 ∧ y 1 < 5 ∧ q 1 = Real.pi * (y 1) ^ 2) ∧
    Matrix.det (fun i j => H a (q i) (t j)) > 0

end

end MathlibPlus.Open.Analysis.CellwiseTransport
