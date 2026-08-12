import Mathlib

open scoped BigOperators

namespace MathlibPlus.Algebra

/--
Formalization of admitted claim 32618.  For a symmetric matrix over
`ZMod 3`, the source's displayed polynomial
`2 * sum_i B_ii x_i^2 + sum_{i<j} B_ij x_i x_j` is the same as
`2 * (xᵀ B x)`: the off-diagonal terms occur twice in the quadratic form
and `4 = 1` in `ZMod 3`.  The quadratic-form presentation keeps the
polarization proof kernel-transparent.
-/
theorem claim32618_quadraticTransporterPolar
    (B : Matrix (Fin 5) (Fin 5) (ZMod 3))
    (hB : ∀ i j, B i j = B j i)
    (x h : Fin 5 → ZMod 3) :
    let qform : (Fin 5 → ZMod 3) → ZMod 3 := fun y =>
      ∑ i, ∑ j, y i * B i j * y j
    let f : (Fin 5 → ZMod 3) → ZMod 3 := fun y => 2 * qform y
    f (x + h) - f x - f h =
      ∑ i, ∑ j, x i * B i j * h j := by
  dsimp
  have hswap :
      (∑ i, ∑ j, h i * B i j * x j) =
        ∑ i, ∑ j, x i * B i j * h j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    rw [hB]
    ring
  have hpolar :
      (∑ i, ∑ j, (x i + h i) * B i j * (x j + h j)) -
          (∑ i, ∑ j, x i * B i j * x j) -
          (∑ i, ∑ j, h i * B i j * h j) =
        (∑ i, ∑ j, x i * B i j * h j) +
          (∑ i, ∑ j, h i * B i j * x j) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  calc
    2 * (∑ i, ∑ j, (x i + h i) * B i j * (x j + h j)) -
          2 * (∑ i, ∑ j, x i * B i j * x j) -
          2 * (∑ i, ∑ j, h i * B i j * h j) =
        2 * ((∑ i, ∑ j, (x i + h i) * B i j * (x j + h j)) -
          (∑ i, ∑ j, x i * B i j * x j) -
          (∑ i, ∑ j, h i * B i j * h j)) := by ring
    _ = 2 * ((∑ i, ∑ j, x i * B i j * h j) +
          (∑ i, ∑ j, h i * B i j * x j)) := by rw [hpolar]
    _ = ∑ i, ∑ j, x i * B i j * h j := by
      rw [hswap]
      let A : ZMod 3 := ∑ i, ∑ j, x i * B i j * h j
      change 2 * (A + A) = A
      calc
        2 * (A + A) = 4 * A := by ring
        _ = A := by
          have h4 : (4 : ZMod 3) = 1 := by decide
          rw [h4, one_mul]

end MathlibPlus.Algebra
