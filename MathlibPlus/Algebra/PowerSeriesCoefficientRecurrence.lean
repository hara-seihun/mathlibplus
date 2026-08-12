import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic

namespace MathlibPlus.Algebra

open PowerSeries

/--
The coefficient recurrence for the generating function in K-0184.  The
coefficient ring is made explicit as `ℚ`, and the quotient is the formal
power-series quotient (the denominator has constant coefficient one).
-/
theorem fourthOrderCoefficientRecurrence_claim9968 :
    let D : PowerSeries ℚ :=
      C 1 + X + C 4 * X ^ 2 + C 2 * X ^ 3 + C 4 * X ^ 4
    let G : PowerSeries ℚ := (X - C 2 * X ^ 3) * D⁻¹
    let g : ℕ → ℚ := fun n => coeff n G
    g 0 = 0 ∧ g 1 = 1 ∧ g 2 = -1 ∧ g 3 = -5 ∧
      ∀ n : ℕ, g (n + 4) + g (n + 3) + 4 * g (n + 2) +
          2 * g (n + 1) + 4 * g n = 0 := by
  let D : PowerSeries ℚ :=
    C 1 + X + C 4 * X ^ 2 + C 2 * X ^ 3 + C 4 * X ^ 4
  let G : PowerSeries ℚ := (X - C 2 * X ^ 3) * D⁻¹
  let g : ℕ → ℚ := fun n => coeff n G
  change coeff 0 G = 0 ∧ coeff 1 G = 1 ∧ coeff 2 G = -1 ∧ coeff 3 G = -5 ∧
      ∀ n : ℕ, coeff (n + 4) G + coeff (n + 3) G + 4 * coeff (n + 2) G +
          2 * coeff (n + 1) G + 4 * coeff n G = 0
  have hD : constantCoeff D = 1 := by
    simp [D]
  have hD0 : constantCoeff D ≠ 0 := by rw [hD]; norm_num
  have hprod : D * G = X - C 2 * X ^ 3 := by
    dsimp [G]
    calc
      D * ((X - C 2 * X ^ 3) * D⁻¹) =
          (X - C 2 * X ^ 3) * (D * D⁻¹) := by ring
      _ = X - C 2 * X ^ 3 := by rw [PowerSeries.mul_inv_cancel D hD0, mul_one]
  have hcoeff (n : ℕ) :
      coeff n (C 1 * G + X ^ 1 * G + C 4 * (X ^ 2 * G) +
        C 2 * (X ^ 3 * G) + C 4 * (X ^ 4 * G)) =
        coeff n (X - C 2 * X ^ 3) := by
    have hrewrite :
        D * G = C 1 * G + X ^ 1 * G + C 4 * (X ^ 2 * G) +
          C 2 * (X ^ 3 * G) + C 4 * (X ^ 4 * G) := by
      dsimp [D]
      ring
    rw [← hrewrite]
    exact congrArg (coeff n) hprod
  have hcc (T : PowerSeries ℚ) : constantCoeff T = coeff 0 T := by
    exact (congrFun (PowerSeries.coeff_zero_eq_constantCoeff (R := ℚ)) T).symm
  have h0 := hcoeff 0
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X] at h0
  norm_num at h0
  have e0 : coeff 0 G = 0 := by
    rw [hcc G] at h0
    exact h0
  have h1 := hcoeff 1
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X] at h1
  norm_num at h1
  rw [hcc G, e0] at h1
  have e1 : coeff 1 G = 1 := by linarith
  have h2 := hcoeff 2
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X] at h2
  norm_num at h2
  rw [hcc G, e0, e1] at h2
  have e2 : coeff 2 G = -1 := by linarith
  have h3 := hcoeff 3
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X] at h3
  norm_num at h3
  rw [hcc G, e0, e1, e2] at h3
  have e3 : coeff 3 G = -5 := by linarith
  refine ⟨e0, e1, e2, e3, ?_⟩
  intro n
  have hn := hcoeff (n + 4)
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X] at hn
  have hsub2 : n + 4 - 2 = n + 2 := by omega
  have hsub3 : n + 4 - 3 = n + 1 := by omega
  rw [hsub2, hsub3] at hn
  have hneq1 : n + 4 ≠ 1 := by omega
  have hneq3 : n + 4 ≠ 3 := by omega
  simp [hneq1, hneq3] at hn
  linarith

end MathlibPlus.Algebra
