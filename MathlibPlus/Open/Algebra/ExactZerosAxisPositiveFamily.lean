import Mathlib

namespace MathlibPlus.Open.Algebra

/-- The family `Q_m(z) = 1 + z^(4m)` is axis-positive but has all of its zeros off both axes. -/
def exactZerosAxisPositiveFamily : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    let Qm : Polynomial ℤ := 1 + Polynomial.X ^ (4 * m)
    let QmR : Polynomial ℝ := Qm.map (Int.castRingHom ℝ)
    let QmC : Polynomial ℂ := Qm.map (Int.castRingHom ℂ)
    let root : Fin (4 * m) → ℂ := fun j =>
      Complex.exp
        (((((2 * (j : ℕ) + 1 : ℕ) : ℂ) * (Real.pi : ℂ) * Complex.I) /
          ((4 * m : ℕ) : ℂ)))
    (∀ n : ℕ, Odd n → Qm.coeff n = 0) ∧
      (∀ x : ℝ,
        QmR.eval x = 1 + x ^ (4 * m) ∧ 0 < 1 + x ^ (4 * m)) ∧
      (∀ t : ℝ,
        QmC.eval ((t : ℂ) * Complex.I) = ((1 + t ^ (4 * m) : ℝ) : ℂ) ∧
          0 < 1 + t ^ (4 * m)) ∧
      Set.ncard {z : ℂ | QmC.eval z = 0} = 4 * m ∧
      (∀ z : ℂ,
        QmC.eval z = 0 ↔ ∃ j : Fin (4 * m), z = root j) ∧
      (∀ j : Fin (4 * m), (root j).re ≠ 0 ∧ (root j).im ≠ 0)

end MathlibPlus.Open.Algebra
