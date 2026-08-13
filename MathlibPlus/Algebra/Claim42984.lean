import Mathlib

open scoped BigOperators

namespace MathlibPlus.Algebra.Claim42984

/-!
# Exterior-square identity for a finite geometric derivative sum

The source claim leaves the scalar field and the finite index set implicit.  We
make them explicit as a characteristic-zero field and `Fin m`; no positivity,
distinctness, or nonvanishing assumptions are added.
-/

private lemma pair_sum_sq
    {R : Type*} [Field R] [CharZero R] {m : ℕ}
    (x b : Fin m → R) :
    (∑ j : Fin m, ∑ k : Fin m,
        x j * x k * (b k ^ 2 - b j * b k)) =
      (1 / 2 : R) * ∑ j : Fin m, ∑ k : Fin m,
        x j * x k * (b j - b k) ^ 2 := by
  let A : R := ∑ j : Fin m, ∑ k : Fin m,
    x j * x k * (b k ^ 2 - b j * b k)
  let A' : R := ∑ j : Fin m, ∑ k : Fin m,
    x j * x k * (b j ^ 2 - b k * b j)
  have hswap : A = A' := by
    dsimp [A, A']
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  calc
    A = (1 / 2 : R) * (A + A) := by
      have htwo : (2 : R) ≠ 0 := by norm_num
      simp only [div_eq_mul_inv, one_mul, ← two_mul]
      rw [← mul_assoc, inv_mul_cancel₀ htwo, one_mul]
    _ = (1 / 2 : R) * (A + A') := by rw [hswap]
    _ = (1 / 2 : R) *
        ∑ j : Fin m, ∑ k : Fin m,
          (x j * x k * (b k ^ 2 - b j * b k) +
            x j * x k * (b j ^ 2 - b k * b j)) := by
      congr 1
      dsimp [A, A']
      calc
        (∑ j : Fin m, ∑ k : Fin m,
            x j * x k * (b k ^ 2 - b j * b k)) +
            ∑ j : Fin m, ∑ k : Fin m,
              x j * x k * (b j ^ 2 - b k * b j) =
          ∑ j : Fin m,
            ((∑ k : Fin m, x j * x k * (b k ^ 2 - b j * b k)) +
              ∑ k : Fin m, x j * x k * (b j ^ 2 - b k * b j)) :=
          (Finset.sum_add_distrib
            (s := Finset.univ)
            (f := fun j : Fin m => ∑ k : Fin m,
              x j * x k * (b k ^ 2 - b j * b k))
            (g := fun j : Fin m => ∑ k : Fin m,
              x j * x k * (b j ^ 2 - b k * b j))).symm
        _ = ∑ j : Fin m, ∑ k : Fin m,
            (x j * x k * (b k ^ 2 - b j * b k) +
              x j * x k * (b j ^ 2 - b k * b j)) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact (Finset.sum_add_distrib
            (s := Finset.univ)
            (f := fun k : Fin m =>
              x j * x k * (b k ^ 2 - b j * b k))
            (g := fun k : Fin m =>
              x j * x k * (b j ^ 2 - b k * b j))).symm
    _ = (1 / 2 : R) * ∑ j : Fin m, ∑ k : Fin m,
        x j * x k * (b j - b k) ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      ring

/-- Claim 42984: the exterior-square identity for a finite geometric
 derivative sum `G r = ∑ j, c j * b j ^ r`. -/
theorem exteriorSquareGeometricDerivative
    {R : Type*} [Field R] [CharZero R] {m : ℕ}
    (c b : Fin m → R) (r : ℕ) :
    let G : ℕ → R := fun n => ∑ j : Fin m, c j * b j ^ n
    G r * G (r + 2) - G (r + 1) ^ 2 =
      (1 / 2 : R) * ∑ j : Fin m, ∑ k : Fin m,
        c j * c k * (b j - b k) ^ 2 * (b j * b k) ^ r := by
  dsimp
  have hprod :
      (∑ j : Fin m, c j * b j ^ r) *
          (∑ k : Fin m, c k * b k ^ (r + 2)) -
        (∑ j : Fin m, c j * b j ^ (r + 1)) ^ 2 =
      ∑ j : Fin m, ∑ k : Fin m,
        (c j * b j ^ r) * (c k * b k ^ r) *
          (b k ^ 2 - b j * b k) := by
    rw [pow_two, Fintype.sum_mul_sum, Fintype.sum_mul_sum]
    calc
      (∑ j : Fin m, ∑ k : Fin m,
          c j * b j ^ r * (c k * b k ^ (r + 2))) -
          ∑ j : Fin m, ∑ k : Fin m,
            c j * b j ^ (r + 1) * (c k * b k ^ (r + 1)) =
        ∑ j : Fin m,
          ((∑ k : Fin m, c j * b j ^ r * (c k * b k ^ (r + 2))) -
            ∑ k : Fin m, c j * b j ^ (r + 1) *
              (c k * b k ^ (r + 1))) := by
        exact (Finset.sum_sub_distrib
          (s := Finset.univ)
          (f := fun j : Fin m => ∑ k : Fin m,
            c j * b j ^ r * (c k * b k ^ (r + 2)))
          (g := fun j : Fin m => ∑ k : Fin m,
            c j * b j ^ (r + 1) * (c k * b k ^ (r + 1)))).symm
      _ = ∑ j : Fin m, ∑ k : Fin m,
          (c j * b j ^ r * (c k * b k ^ (r + 2)) -
            c j * b j ^ (r + 1) * (c k * b k ^ (r + 1))) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (Finset.sum_sub_distrib
          (s := Finset.univ)
          (f := fun k : Fin m =>
            c j * b j ^ r * (c k * b k ^ (r + 2)))
          (g := fun k : Fin m =>
            c j * b j ^ (r + 1) * (c k * b k ^ (r + 1)))).symm
      _ = ∑ j : Fin m, ∑ k : Fin m,
          (c j * b j ^ r) * (c k * b k ^ r) *
            (b k ^ 2 - b j * b k) := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro k hk
        simp only [pow_add]
        ring
  rw [hprod]
  rw [pair_sum_sq]
  apply congrArg (fun q : R => (1 / 2 : R) * q)
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_pow]
  ring

end MathlibPlus.Algebra.Claim42984
