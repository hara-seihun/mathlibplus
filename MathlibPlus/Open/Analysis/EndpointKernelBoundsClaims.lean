import Mathlib

open Filter Asymptotics
open ArithmeticFunction
open scoped Topology

namespace MathlibPlus.Open.Analysis

/-- Endpoint asymptotics for the all-prime Möbius remainder. -/
def endpointEstimates_claim13398 : Prop :=
  let R : ℂ → ℂ :=
    fun x =>
      ∑' n : {n : ℕ // 0 < n},
        (ArithmeticFunction.moebius n.1 : ℂ) *
          (Complex.exp (-x / (n.1 : ℂ)) - 1 + x / (n.1 : ℂ))
  IsBigO (𝓝[>] (0 : ℝ))
      (fun x : ℝ =>
        R (x : ℂ) - (x : ℂ) ^ 2 / (2 * riemannZeta (2 : ℂ)))
      (fun x : ℝ => (x : ℂ) ^ 3) ∧
    IsBigO (atTop : Filter (Set.Ici (0 : ℝ)))
      (fun x : Set.Ici (0 : ℝ) => R (x.1 : ℂ))
      (fun x : Set.Ici (0 : ℝ) =>
        (x.1 : ℂ) * (Real.log (2 + x.1) : ℂ))

/-- The second derivative of the all-prime Möbius remainder. -/
def differentiatedClassicalReciprocalZetaKernel_claim13400 : Prop :=
  let R : ℂ → ℂ :=
    fun x =>
      ∑' n : {n : ℕ // 0 < n},
        (ArithmeticFunction.moebius n.1 : ℂ) *
          (Complex.exp (-x / (n.1 : ℂ)) - 1 + x / (n.1 : ℂ))
  ∀ x : ℂ,
    deriv (deriv R) x =
        (∑' n : {n : ℕ // 0 < n},
          (ArithmeticFunction.moebius n.1 : ℂ) /
              (n.1 : ℂ) ^ 2 * Complex.exp (-x / (n.1 : ℂ))) ∧
      (∑' n : {n : ℕ // 0 < n},
        (ArithmeticFunction.moebius n.1 : ℂ) /
            (n.1 : ℂ) ^ 2 * Complex.exp (-x / (n.1 : ℂ))) =
        ∑' k : ℕ,
          (-x) ^ k /
            ((Nat.factorial k : ℂ) * riemannZeta ((k + 2 : ℕ) : ℂ))

/-- Unbounded positive and negative values, with arbitrarily many sign changes. -/
def unconditionalTwoSidedOscillation_claim13402 : Prop :=
  let R : ℝ → ℝ :=
    fun x =>
      ∑' n : {n : ℕ // 0 < n},
        (ArithmeticFunction.moebius n.1 : ℝ) *
          (Real.exp (-x / (n.1 : ℝ)) - 1 + x / (n.1 : ℝ))
  let positive : Set ℝ := {x | 0 < x ∧ 0 < R x}
  let negative : Set ℝ := {x | 0 < x ∧ R x < 0}
  (¬ BddAbove positive) ∧
    (¬ BddAbove negative) ∧
    ∀ N : ℕ, ∃ x : Fin (N + 1) → ℝ,
      (∀ i, 0 < x i) ∧
        (∀ ⦃i j⦄, i < j → x i < x j) ∧
          (∀ i : Fin N, R (x i.castSucc) * R (x i.succ) < 0)

/-- Endpoint asymptotics for the all-prime reciprocal-zeta kernel. -/
def elementaryKernelEndpointBounds_claim13407 : Prop :=
  let K : ℂ → ℂ :=
    fun x =>
      ∑' n : {n : ℕ // 0 < n},
        (ArithmeticFunction.moebius n.1 : ℂ) /
            (n.1 : ℂ) ^ 2 * Complex.exp (-x / (n.1 : ℂ))
  IsBigO (𝓝[>] (0 : ℝ))
      (fun x : ℝ => K (x : ℂ) - 1 / riemannZeta (2 : ℂ))
      (fun x : ℝ => (x : ℂ)) ∧
    IsBigO (atTop : Filter ℝ)
      (fun x : ℝ => K (x : ℂ))
      (fun x : ℝ => (x : ℂ)⁻¹)

end MathlibPlus.Open.Analysis
