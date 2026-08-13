import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim15128

/-- Exact local division identity. -/
theorem exact_division_identity {K : Type*} [Field K]
    {P U S T R Q : K}
    (hQ : Q = S * T) (hP : P = S * U + R)
    (hQ0 : Q ≠ 0) (hT0 : T ≠ 0) :
    P / Q - U / T = R / Q := by
  rw [hP, hQ]
  have hST0 : S * T ≠ 0 := by
    rw [← hQ]
    exact hQ0
  have hS0 : S ≠ 0 := by
    intro hS
    exact hST0 (hS ▸ zero_mul T)
  field_simp [hS0, hT0]
  ring

/-- Inexact local division identity. -/
theorem inexact_division_identity {K : Type*} [Field K]
    {P U S T D R Q : K}
    (hQ : Q = S * T + D) (hP : P = S * U + R)
    (hQ0 : Q ≠ 0) (hT0 : T ≠ 0) :
    P / Q - U / T = (R * T - U * D) / (Q * T) := by
  rw [hP]
  field_simp [hQ0, hT0]
  rw [hQ]
  ring

end MathlibPlus.Algebra.Claim15128

namespace MathlibPlus.Algebra.Claim19361

/-- A diagonal cell state given by a weighted sum is homogeneous of degree one in the weights. -/
theorem diagonal_cell_homogeneous {ι R V : Type*} [Fintype ι]
    [Semiring R] [AddCommMonoid V] [Module R V] (X : ι → V) :
    let cell : (ι → R) → V := fun x => ∑ i, x i • X i
    ∀ (c : R) (x : ι → R), cell (c • x) = c • cell x := by
  dsimp
  intro c x
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_smul]

end MathlibPlus.Algebra.Claim19361
