import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.LinearAlgebra.LagrangianScatteringBatch

private noncomputable def bilinearForm {N : ℕ}
    (D : Matrix (Fin N) (Fin N) ℝ) (x y : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, x i * D i j * y j

private noncomputable def doubledForm {N : ℕ}
    (D : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin (2 * N)) (Fin (2 * N)) ℝ :=
  fun i j =>
    if hi : i.val < N then
      if hj : j.val < N then D ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
    else if hj : j.val < N then 0
    else -D ⟨i.val - N, by omega⟩ ⟨j.val - N, by omega⟩

private noncomputable def graphVector {N : ℕ}
    (U : Matrix (Fin N) (Fin N) ℝ) (x : Fin N → ℝ) : Fin (2 * N) → ℝ :=
  fun i =>
    if hi : i.val < N then x ⟨i.val, hi⟩
    else (Matrix.mulVec U x) ⟨i.val - N, by omega⟩

private noncomputable def graphIsLagrangian {N : ℕ}
    (D U : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  (∀ x y : Fin N → ℝ,
    bilinearForm (doubledForm D) (graphVector U x) (graphVector U y) = 0) ∧
  (∀ v : Fin (2 * N) → ℝ,
    (∀ x : Fin N → ℝ,
      bilinearForm (doubledForm D) v (graphVector U x) = 0) →
    ∃ x : Fin N → ℝ, v = graphVector U x)

/-- Claim 17568: the graph of a Krein isometry is Lagrangian. -/
def claim17568 : Prop :=
  ∀ (N : ℕ) (D U : Matrix (Fin N) (Fin N) ℝ),
    D.transpose = D → D.det ≠ 0 → U.transpose * D * U = D →
    graphIsLagrangian D U

/-- Claim 17570: the normalized affine spinor is exactly symplectic. -/
def claim17570 : Prop :=
  ∀ (z s : ℂ),
    let a : ℂ := ((2 * z + 5) * (2 * z + 3)) / (4 * Real.pi * (2 * z - 1))
    let A : Matrix (Fin 2) (Fin 2) ℂ := fun i j =>
      if i.val = 0 ∧ j.val = 0 then 0
      else if i.val = 0 ∧ j.val = 1 then 1
      else if i.val = 1 ∧ j.val = 0 then a
      else 0
    let J : Matrix (Fin 2) (Fin 2) ℂ := fun i j =>
      if i.val = 0 ∧ j.val = 1 then 1
      else if i.val = 1 ∧ j.val = 0 then -1
      else 0
    2 * z - 1 ≠ 0 → s ≠ 0 → s ^ 2 = -a →
      let U := (s⁻¹) • A
      U.transpose * J * U = J

/-- Claim 17572: the symmetric relative-position channel. -/
def claim17572 : Prop :=
  ∀ (N : ℕ) (D U V : Matrix (Fin N) (Fin N) ℝ),
    D.transpose = D →
    U.transpose * D * U = D → V.transpose * D * V = D →
    let S : Matrix (Fin N) (Fin N) ℝ :=
      (1 / 2 : ℝ) • ((U - V).transpose * D * (U - V))
    S.transpose = S ∧
      ((1 / 2 : ℝ) • ((U - V).transpose * D * (U - V))) =
        ((1 / 2 : ℝ) • ((V - U).transpose * D * (V - U))) ∧
      ((1 / 2 : ℝ) • ((U - U).transpose * D * (U - U))) = 0

end MathlibPlus.Open.LinearAlgebra.LagrangianScatteringBatch
