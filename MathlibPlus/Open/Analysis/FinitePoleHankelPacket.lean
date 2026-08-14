import Mathlib

open scoped BigOperators Topology
open Filter MeasureTheory
noncomputable section

namespace MathlibPlus.Open.K0066

/-- Claim 8123: finite-product coefficients, reciprocal coefficients, and shifted minors. -/
def finiteProductReciprocalDefinitions_8123 : Prop :=
  ∀ (N : ℕ) (x : Fin N → ℂ) (r k : ℕ),
    (∀ i j, i ≠ j → x i ≠ x j) →
    (∀ i, x i ≠ 0) →
    let E : Polynomial ℂ :=
      ∏ ν : Fin N, (1 + Polynomial.C (x ν) * Polynomial.X)
    let e : ℕ → ℂ := fun n => Polynomial.coeff E n
    ∃ h : ℕ → ℂ, ∃ D : ℂ,
      (∀ n : ℕ,
        (∑ i ∈ Finset.range (n + 1),
            (-1 : ℂ) ^ i * e i * h (n - i)) =
          if n = 0 then 1 else 0) ∧
      D = Matrix.det (fun i j : Fin r => e (k + j.val - i.val))

/-- Claim 8124: the exact finite pole-subset expansion of the determinant. -/
def exactPoleSubsetFormula_8124 : Prop :=
  ∀ (N r k : ℕ) (x : Fin N → ℂ),
    k ≤ N →
    (∀ i j, i ≠ j → x i ≠ x j) →
    (∀ i, x i ≠ 0) →
    let E : Polynomial ℂ :=
      ∏ ν : Fin N, (1 + Polynomial.C (x ν) * Polynomial.X)
    let e : ℕ → ℂ := fun n => Polynomial.coeff E n
    Matrix.det (fun i j : Fin r => e (k + j.val - i.val)) =
      ∑ I ∈
          (Finset.univ : Finset (Fin N)).powerset.filter
            (fun I => I.card = k),
        (∏ i ∈ I, (x i) ^ r) *
          ∏ i ∈ I, ∏ m ∈ (Finset.univ \ I),
            (1 - x m / x i)⁻¹

/-- Claim 8126: the rectangular dual Jacobi--Trudi determinant identity. -/
def dualJacobiTrudiIdentity_8126 : Prop :=
  ∀ (r k : ℕ) (e h : ℕ → ℂ),
    (∀ n : ℕ,
      (∑ i ∈ Finset.range (n + 1),
          (-1 : ℂ) ^ i * e i * h (n - i)) =
        if n = 0 then 1 else 0) →
    let Dₑ : ℂ := Matrix.det (fun i j : Fin r => e (k + j.val - i.val))
    let Dₕ : ℂ := Matrix.det (fun i j : Fin k => h (r + j.val - i.val))
    Dₑ = Dₕ ∧
      ∀ (a₀ : ℂ), a₀ ≠ 0 →
        Matrix.det (fun i j : Fin r => a₀ * e (k + j.val - i.val)) /
            a₀ ^ r = Dₑ

/-- Claim 8129: a simple positive pole head with a contour-supported remainder. -/
def simplePositivePoleHeadContourRemainder_8129 : Prop :=
  ∀ (k : ℕ) (x : Fin k → ℝ) (c : Fin k → ℝ) (y M : ℝ)
    (h : ℕ → ℂ) (ν : ComplexMeasure ℂ),
    0 < y → 0 ≤ M →
    (∀ j, y < x j) →
    (∀ i j, i.val < j.val → x j < x i) →
    (∀ j, c j ≠ 0 ∧ Real.sign (c j) = (-1 : ℝ) ^ j.val) →
    ν.variation {z : ℂ | ‖z‖ ≠ y} = 0 →
    ν.variation Set.univ ≤ ENNReal.ofReal M →
    ∀ m : ℕ,
      h m =
        ∑ j : Fin k, (c j : ℂ) * (x j : ℂ) ^ m +
          VectorMeasure.integral ν (fun z : ℂ => z ^ m)
            (ContinuousLinearMap.lsmul ℝ ℂ)

/-- Claim 8135: equal-modulus deleted poles produce a noncontractive cycling minor. -/
def equalModulusMixedShellCounterfeit_8135 : Prop :=
  let E : Polynomial ℂ :=
    (1 + Polynomial.X) * (1 + Polynomial.X ^ 2)
  let Q : Polynomial ℂ := 1 + Polynomial.X ^ 2
  let h : ℕ → ℂ := fun n =>
    if n % 2 = 0 then (-1 : ℂ) ^ (n / 2) else 0
  let m : ℕ → ℂ := fun n =>
    Matrix.det (fun i j : Fin 1 => h (n + 1 + j.val - i.val))
  E = (1 + Polynomial.X) * Q ∧
    Polynomial.eval Complex.I Q = 0 ∧
    Polynomial.eval (-Complex.I) Q = 0 ∧
    ‖Complex.I‖ = ‖-Complex.I‖ ∧
    (∀ n : ℕ,
      m n = if n % 4 = 0 then 0 else
        if n % 4 = 1 then -1 else
          if n % 4 = 2 then 0 else 1) ∧
    (∃ᶠ n : ℕ in atTop, m n = -1) ∧
    ¬ ∃ C q : ℝ, 0 ≤ C ∧ 0 ≤ q ∧ q < 1 ∧
      ∀ n : ℕ, ‖m n‖ ≤ C * q ^ n

/-- Claim 8142: separated reciprocal poles and an explicitly controlled Hankel
perturbation preserve the positive pole determinant. -/
def fixedShiftReciprocalPolePerturbationCriterion_8142 : Prop :=
  ∀ (k r : ℕ) (γ c : Fin k → ℝ) (H M : ℝ)
    (h ε : ℕ → ℝ),
    0 < k → k ≤ r → 1 < H → 0 ≤ M →
    (∀ j, 0 < γ j) →
    (∀ i j, i.val < j.val → γ j < γ i) →
    (∀ j, c j ≠ 0 ∧ Real.sign (c j) = (-1 : ℝ) ^ j.val) →
    (∀ n : ℕ,
      h n =
        ∑ j : Fin k, c j * (γ j)⁻¹ ^ (2 * n) + ε n) →
    (∀ n : ℕ, |ε n| ≤ M * (H⁻¹) ^ (2 * n)) →
    let Q : Matrix (Fin k) (Fin k) ℝ := fun i j =>
      ∑ l : Fin k,
        c l * (γ l)⁻¹ ^
          (2 * (r + (k - 1 - i.val) + j.val))
    let E : Matrix (Fin k) (Fin k) ℝ := fun i j =>
      ε (r + (k - 1 - i.val) + j.val)
    let Vplus : Matrix (Fin k) (Fin k) ℝ := fun i l =>
      (γ l) ^ (2 * i.val)
    let D : Matrix (Fin k) (Fin k) ℝ := fun i j =>
      if i = j then c i * (γ i)⁻¹ ^ (2 * (r + k - 1)) else 0
    let Vminus : Matrix (Fin k) (Fin k) ℝ := fun l j =>
      (γ l)⁻¹ ^ (2 * j.val)
    Matrix.det Q > 0 ∧
      Q = Vplus * D * Vminus ∧
      ((∀ i : Fin k, ∑ j : Fin k, |(Q⁻¹ * E) i j| < 1) →
        Matrix.det (Q + E) > 0) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ R : ℕ,
          (∑ i : Fin k, ∑ j : Fin k,
            |ε (R + (k - 1 - i.val) + j.val)|) ≤
            C * (H⁻¹) ^ (2 * R)

end MathlibPlus.Open.K0066
