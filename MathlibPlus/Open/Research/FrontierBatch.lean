import Mathlib

open scoped BigOperators Topology Interval
open BigOperators
open MeasureTheory Filter

namespace MathlibPlus.Open.Research

def leastJointSquareShiftGlobalStrictTailObstruction : Prop :=
  let q : ℕ → ℕ := fun n =>
    if n ≤ 4 then 2 * Nat.factorial (n + 2) else 2 * Nat.factorial (n + 2) + 1
  let p : ℕ → ℕ := fun n =>
    if n ≤ 4 then n + 1 else n + 2
  let m : ℕ → ℚ := fun n =>
    (1 / 2 : ℚ) * ∏ i ∈ Finset.range n, (q i : ℚ)
  let μ : ℕ → ℕ := fun n => ∏ i ∈ Finset.range n, p i
  (∀ n : ℕ, 0 < m n) ∧
    (∀ n : ℕ, 0 < μ n) ∧
    StrictMono q ∧ StrictMono p ∧
    (m 0, m 1, m 2, m 3, m 4, m 5) =
      ((1 / 2 : ℚ), 2, 24, 1152, 276480, 398131200) ∧
    (μ 0, μ 1, μ 2, μ 3, μ 4, μ 5) =
      (1, 1, 2, 6, 24, 120) ∧
    (∀ n : ℕ, m (n + 1) = (q n : ℚ) * m n) ∧
    (∀ n : ℕ, μ (n + 1) = p n * μ n) ∧
    (∀ n : ℕ, n ≤ 4 →
      q n = 2 * Nat.factorial (n + 2) ∧ p n = n + 1) ∧
    (∀ n : ℕ, 5 ≤ n →
      q n ≠ 2 * Nat.factorial (n + 2) ∧ p n ≠ n + 1)

def adaptiveTranscriptPrefixSubgaussianChaining : Prop :=
  ∀ (d b : ℕ), 1 ≤ d → 1 ≤ b →
    ∀ (A : Fin d → Type*) (hA : ∀ i : Fin d, Fintype (A i))
      (C : Type*) [Fintype C] (hC : Nonempty C)
      (code : C → ∀ i : Fin d, A i),
      Function.Injective code →
      (∀ i : Fin d, @Fintype.card (A i) (hA i) ≤ b) →
      letI : DecidableEq C := Classical.decEq C
      let ell : C → C → ℕ := fun x y =>
        if x = y then 0 else
          sInf {n : ℕ | ∃ i : Fin d, i.1 = n ∧ code x i ≠ code y i}
      let rho : C → C → ℝ := fun x y =>
        if x = y then 0 else Real.rpow 2 (-(ell x y : ℝ))
      (∀ x, rho x x = 0) ∧
        (∀ x y, rho x y = rho y x) ∧
        (∀ x y, 0 ≤ rho x y) ∧
        (∀ x y z, rho x z ≤ max (rho x y) (rho y z)) ∧
        (∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) (X : C → Ω → ℝ),
          μ Set.univ = 1 →
          (∀ x, Integrable (X x) μ) →
          (∀ x, ∫ ω, X x ω ∂μ = 0) →
          (∀ x y : C, ∀ lambda : ℝ,
            ∫ ω, Real.exp (lambda * (X x ω - X y ω)) ∂μ ≤
              Real.exp (lambda ^ 2 * rho x y ^ 2 / 2)) →
          (∫ ω, sSup (Set.range (fun x => X x ω)) ∂μ) ≤
            Real.sqrt (2 * Real.log (b : ℝ)) *
                ∑ m ∈ Finset.Icc 1 d,
                  Real.rpow 2 (-((m - 1 : ℕ) : ℝ)) *
                    Real.sqrt (m : ℝ) ∧
            (∫ ω, sSup (Set.range (fun x => X x ω)) ∂μ) ≤
              4 * Real.sqrt (2 * Real.log (b : ℝ)))

end MathlibPlus.Open.Research
