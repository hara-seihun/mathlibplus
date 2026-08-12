import Mathlib

namespace MathlibPlus.Algebra.ShellDivision

/--
Claim 3289, exact shell-division identity.  The numerator and remainder may
be vector-valued: division by a scalar is represented by scalar multiplication
by its inverse.  The nonvanishing hypotheses make the source's rational
expression well-defined (Lean otherwise totalizes inverse at zero).
-/
theorem shellDivisionIdentity_claim3289
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {s t d q : K} {u r p : V}
    (ht : t ≠ 0) (hq : q ≠ 0)
    (hq' : q = s * t + d) (hp : p = s • u + r) :
    q⁻¹ • p - t⁻¹ • u = (q * t)⁻¹ • (t • r - d • u) := by
  have hqt : q * t ≠ 0 := mul_ne_zero hq ht
  have hsum : s * t + d ≠ 0 := by rwa [← hq']
  have hcoeff : q⁻¹ * s - t⁻¹ = -(q * t)⁻¹ * d := by
    rw [hq']
    field_simp [ht, hsum]
    ring
  have hrest : q⁻¹ = (q * t)⁻¹ * t := by
    field_simp [ht, hq]
  calc
    q⁻¹ • p - t⁻¹ • u = q⁻¹ • (s • u + r) - t⁻¹ • u := by rw [hp]
    _ = (q⁻¹ * s - t⁻¹) • u + q⁻¹ • r := by
      rw [smul_add, smul_smul, sub_smul]
      abel
    _ = (-(q * t)⁻¹ * d) • u + ((q * t)⁻¹ * t) • r := by rw [hcoeff, hrest]
    _ = (q * t)⁻¹ • (t • r - d • u) := by
      have hneg : -(q * t)⁻¹ * d = -((q * t)⁻¹ * d) := by ring
      rw [hneg, neg_smul, smul_sub, smul_smul, smul_smul]
      module

/-- Claim 3289: with exact denominator division, the discrepancy is `R / Q`. -/
theorem shellDivisionExactDenominator_claim3289
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {s t d q : K} {u r p : V}
    (ht : t ≠ 0) (hq : q ≠ 0)
    (hq' : q = s * t + d) (hp : p = s • u + r) (hd : d = 0) :
    q⁻¹ • p - t⁻¹ • u = q⁻¹ • r := by
  have hrest : q⁻¹ = (q * t)⁻¹ * t := by
    field_simp [ht, hq]
  calc
    q⁻¹ • p - t⁻¹ • u = (q * t)⁻¹ • (t • r - d • u) :=
      shellDivisionIdentity_claim3289 ht hq hq' hp
    _ = (q * t)⁻¹ • (t • r) := by rw [hd, zero_smul, sub_zero]
    _ = ((q * t)⁻¹ * t) • r := by rw [smul_smul]
    _ = q⁻¹ • r := by rw [← hrest]

/-- Claim 3289: if both exact divisions remove a common factor, the rational
function is unchanged. -/
theorem shellDivisionExactCommonFactor_claim3289
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {s t d q : K} {u r p : V}
    (ht : t ≠ 0) (hq : q ≠ 0)
    (hq' : q = s * t + d) (hp : p = s • u + r)
    (hd : d = 0) (hr : r = 0) :
    q⁻¹ • p = t⁻¹ • u := by
  have h := shellDivisionExactDenominator_claim3289 ht hq hq' hp hd
  rw [hr, smul_zero] at h
  exact sub_eq_zero.mp h

end MathlibPlus.Algebra.ShellDivision
