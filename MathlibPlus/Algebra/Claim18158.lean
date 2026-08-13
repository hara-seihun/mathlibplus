import Mathlib

namespace MathlibPlus.Algebra

open Polynomial

private lemma coeff_mul_X_pred {R : Type*} [Semiring R] (p : R[X]) (k : ℕ)
    (hk : 1 ≤ k) :
    (p * X).coeff k = p.coeff (k - 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  simpa using coeff_mul_X p j

/-- The elementary-symmetric Pascal recursion from claim 18158.  The local
coefficient definition expands `e_k^(m)` as the coefficient of the product
`∏_{j=1}^{m-1} (1 + (2j)⁻¹ X)` over `ℚ`. -/
theorem elementary_symmetric_pascal_claim18158
    (m k : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k) (hkm : k < m - 1) :
    let e : ℕ → ℕ → ℚ := fun m k =>
      (∏ j ∈ Finset.Icc (1 : ℕ) (m - 1),
        (Polynomial.C 1 + Polynomial.C ((2 * (j : ℚ))⁻¹) * Polynomial.X)).coeff k
    e m k = e (m - 1) k + (2 * ((m - 1 : ℕ) : ℚ))⁻¹ * e (m - 1) (k - 1) := by
  dsimp
  have hIcc : Finset.Icc (1 : ℕ) (m - 1) =
      insert (m - 1) (Finset.Icc (1 : ℕ) (m - 2)) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : m - 1 ∉ Finset.Icc (1 : ℕ) (m - 2) := by
    simp only [Finset.mem_Icc]
    omega
  have hprev : (m - 1) - 1 = m - 2 := by omega
  rw [hIcc, Finset.prod_insert hnot]
  let P : ℚ[X] := ∏ j ∈ Finset.Icc (1 : ℕ) (m - 2),
    (Polynomial.C 1 + Polynomial.C ((2 * (j : ℚ))⁻¹) * Polynomial.X)
  have hcoef : ∀ q : ℕ, 1 ≤ q →
      ((Polynomial.C 1 + Polynomial.C ((2 * ((m - 1 : ℕ) : ℚ))⁻¹) * Polynomial.X) * P).coeff q =
        P.coeff q + (2 * ((m - 1 : ℕ) : ℚ))⁻¹ * P.coeff (q - 1) := by
    intro q hq
    calc
      ((Polynomial.C 1 + Polynomial.C ((2 * ((m - 1 : ℕ) : ℚ))⁻¹) * Polynomial.X) * P).coeff q =
          (Polynomial.C 1 * P).coeff q +
            (Polynomial.C ((2 * ((m - 1 : ℕ) : ℚ))⁻¹) * Polynomial.X * P).coeff q := by
        rw [add_mul, coeff_add]
      _ = P.coeff q +
          (Polynomial.C ((2 * ((m - 1 : ℕ) : ℚ))⁻¹) *
            (Polynomial.X * P)).coeff q := by
        rw [coeff_C_mul, ← mul_assoc]
        simp
      _ = P.coeff q +
          (2 * ((m - 1 : ℕ) : ℚ))⁻¹ * P.coeff (q - 1) := by
        rw [coeff_C_mul]
        have hmul : (Polynomial.X * P).coeff q = P.coeff (q - 1) := by
          rw [mul_comm, coeff_mul_X_pred P q hq]
        rw [hmul]
  change
    ((Polynomial.C 1 + Polynomial.C ((2 * ((m - 1 : ℕ) : ℚ))⁻¹) * Polynomial.X) * P).coeff k =
      (∏ j ∈ Finset.Icc (1 : ℕ) (m - 1 - 1),
        (Polynomial.C 1 + Polynomial.C ((2 * (j : ℚ))⁻¹) * Polynomial.X)).coeff k +
        (2 * ((m - 1 : ℕ) : ℚ))⁻¹ *
          (∏ j ∈ Finset.Icc (1 : ℕ) (m - 1 - 1),
            (Polynomial.C 1 + Polynomial.C ((2 * (j : ℚ))⁻¹) * Polynomial.X)).coeff (k - 1)
  rw [hprev]
  change
    ((Polynomial.C 1 + Polynomial.C ((2 * ((m - 1 : ℕ) : ℚ))⁻¹) * Polynomial.X) * P).coeff k =
      P.coeff k + (2 * ((m - 1 : ℕ) : ℚ))⁻¹ * P.coeff (k - 1)
  exact hcoef k hk

end MathlibPlus.Algebra
