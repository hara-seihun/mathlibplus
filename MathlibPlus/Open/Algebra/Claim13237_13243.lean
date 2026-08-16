import Mathlib

namespace MathlibPlus.Open.Algebra

private noncomputable def batchP : Polynomial ℤ :=
  Polynomial.X ^ 14 - Polynomial.X ^ 12 + Polynomial.X ^ 7 - Polynomial.X ^ 2 + 1

private noncomputable def batchQ : Polynomial ℤ :=
  Polynomial.X ^ 7 - 8 * Polynomial.X ^ 5 + 19 * Polynomial.X ^ 3 - 12 * Polynomial.X + 1

noncomputable def batchMahlerMeasure (p : Polynomial ℤ) : ℝ :=
  ((p.map (algebraMap ℤ ℂ)).roots.map (fun z => max (1 : ℝ) ‖z‖)).prod

noncomputable def batchUnitRootCount (p : Polynomial ℂ) : ℕ := by
  classical
  exact (p.roots.filter (fun z => ‖z‖ = (1 : ℝ))).card

/-- Claim 13237: the fixed polynomial P is irreducible over ℚ. -/
def claim13237 : Prop :=
  Irreducible (batchP.map (algebraMap ℤ ℚ))

/-- Claim 13238: the fixed polynomial P has the stated exterior/interior/unit-circle roots. -/
def claim13238 : Prop :=
  let p : Polynomial ℂ := batchP.map (algebraMap ℤ ℂ)
  ∃ z : ℂ,
    p.natDegree = 14 ∧
    p.IsRoot z ∧
    1 < ‖z‖ ∧
    z.im = 0 ∧
    z.re < 0 ∧
    (1.202 : ℝ) < ‖z‖ ∧
    ‖z‖ < 1.203 ∧
    (∀ w : ℂ, p.IsRoot w → 1 < ‖w‖ → w = z) ∧
    p.IsRoot z⁻¹ ∧
    ‖z⁻¹‖ < 1 ∧
    (∀ w : ℂ, p.IsRoot w → ‖w‖ < 1 → w = z⁻¹) ∧
    (∀ w : ℂ, p.IsRoot w → w ≠ z → w ≠ z⁻¹ → ‖w‖ = 1) ∧
    batchUnitRootCount p = 12

/-- Claim 13239: the fixed polynomial P has the stated Mahler measure. -/
def claim13239 : Prop :=
  (1.2026167436 : ℝ) ≤ batchMahlerMeasure batchP ∧
    batchMahlerMeasure batchP < 1.2026167437 ∧
    (1.202 : ℝ) < batchMahlerMeasure batchP ∧
    batchMahlerMeasure batchP < 1.203 ∧
    (1.203 : ℝ) < 1.3

/-- Claim 13243: no integer symmetric matrix has characteristic polynomial Q times a
polynomial whose complex roots all lie in [-2,2]. -/
def claim13243 : Prop :=
  ¬ ∃ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (C : Polynomial ℤ),
    (∀ i j : Fin n, A i j = A j i) ∧
    Matrix.charpoly A = batchQ * C ∧
    (∀ z : ℂ,
      (C.map (algebraMap ℤ ℂ)).IsRoot z →
        z.im = 0 ∧ (-2 : ℝ) ≤ z.re ∧ z.re ≤ 2)

end MathlibPlus.Open.Algebra
