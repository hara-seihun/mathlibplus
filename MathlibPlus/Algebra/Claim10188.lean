import MathlibPlus.Basic

namespace MathlibPlus.Algebra

open scoped BigOperators

/-- The finite geometric exterior-square identity from admitted claim 10188.
The characteristic-zero field hypothesis makes the displayed factor `1/2`
unambiguous. -/
theorem claim10188_geometricExteriorSquareIdentity
    {R ι : Type*} [Field R] [CharZero R] [Fintype ι]
    (c b : ι → R) (r : ℕ) :
    (∑ j : ι, c j * b j ^ r) * (∑ j : ι, c j * b j ^ (r + 2)) -
        (∑ j : ι, c j * b j ^ (r + 1)) ^ 2 =
      (1 / 2 : R) * ∑ j : ι, ∑ k : ι,
        c j * c k * (b j - b k) ^ 2 * (b j * b k) ^ r := by
  classical
  have hbase (x y : R) :
      (x - y)^2 * (x*y)^r =
        x^r * y^(r+2) + x^(r+2) * y^r - 2 * x^(r+1) * y^(r+1) := by
    rw [mul_pow]
    simp only [pow_two]
    ring_nf
  have hterm (j k : ι) :
      c j * c k * (b j - b k)^2 * (b j*b k)^r =
        c j*c k * (b j^r * b k^(r+2) + b j^(r+2) * b k^r -
          2 * b j^(r+1) * b k^(r+1)) := by
    calc
      _ = c j * c k * ((b j - b k)^2 * (b j*b k)^r) := by ring
      _ = _ := by rw [hbase]
  have hswap (f : ι → ι → R) :
      (∑ x : ι, ∑ i : ι, f x i) = ∑ x : ι, ∑ i : ι, f i x := by
    rw [Finset.sum_comm]
  simp_rw [hterm]
  simp only [mul_add, mul_sub]
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hL1 :
      (∑ x : ι, ∑ i : ι, c i * b i ^ r * (c x * b x ^ (r + 2))) =
        ∑ x : ι, ∑ i : ι, c x * c i * (b x ^ (r + 2) * b i ^ r) := by
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hS1 :
      (∑ x : ι, ∑ i : ι, c x * c i * (b x ^ r * b i ^ (r + 2))) =
        ∑ x : ι, ∑ i : ι, c i * b i ^ r * (c x * b x ^ (r + 2)) := by
    calc
      _ = ∑ x : ι, ∑ i : ι,
          c i * c x * (b i ^ r * b x ^ (r + 2)) := hswap _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have hS3 :
      (∑ x : ι, ∑ i : ι,
          c x * c i * (2 * b x ^ (r + 1) * b i ^ (r + 1))) =
        2 * (∑ x : ι, ∑ i : ι,
          c i * b i ^ (r + 1) * (c x * b x ^ (r + 1))) := by
    calc
      _ = ∑ x : ι, ∑ i : ι,
          2 * (c i * b i ^ (r + 1) * (c x * b x ^ (r + 1))) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by
        simp_rw [← Finset.mul_sum]
  rw [hS1, ← hL1, hS3]
  have htwo : (2 : R) ≠ 0 := by norm_num
  field_simp [htwo]
  ring

end MathlibPlus.Algebra
