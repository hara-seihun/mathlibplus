import Mathlib

namespace MathlibPlus.Analysis.EvenLoewner

/-- The total even prime-side Loewner matrix attached to a logarithmic derivative
`L` and a finite family of distinct positive rates.  The diagonal is the confluent
value specified in the source. -/
noncomputable def totalEvenLoewnerMatrix
    {n : ℕ} (L : ℝ → ℝ) (rate : Fin n → ℝ)
    (_hpos : ∀ i, 0 < rate i) (_hinj : Function.Injective rate) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    if i = j then
      2 * (L (rate i) / rate i - deriv L (rate i))
    else
      4 * (rate j * L (rate i) - rate i * L (rate j)) /
        (rate j ^ 2 - rate i ^ 2)

@[simp]
theorem totalEvenLoewnerMatrix_diagonal
    {n : ℕ} (L : ℝ → ℝ) (rate : Fin n → ℝ)
    (hpos : ∀ i, 0 < rate i) (hinj : Function.Injective rate) (i : Fin n) :
    totalEvenLoewnerMatrix L rate hpos hinj i i =
      2 * (L (rate i) / rate i - deriv L (rate i)) := by
  simp [totalEvenLoewnerMatrix]

@[simp]
theorem totalEvenLoewnerMatrix_offDiagonal
    {n : ℕ} (L : ℝ → ℝ) (rate : Fin n → ℝ)
    (hpos : ∀ i, 0 < rate i) (hinj : Function.Injective rate) {i j : Fin n}
    (hij : i ≠ j) :
    totalEvenLoewnerMatrix L rate hpos hinj i j =
      4 * (rate j * L (rate i) - rate i * L (rate j)) /
        (rate j ^ 2 - rate i ^ 2) := by
  simp [totalEvenLoewnerMatrix, hij]

end MathlibPlus.Analysis.EvenLoewner
