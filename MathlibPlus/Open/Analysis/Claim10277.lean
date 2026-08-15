import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.Claim10277

noncomputable section

/-- The partial Mertens sum `A_n = ∑_{k ≤ n} μ(k) / k`. -/
def mobiusPartial (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (1 : ℕ) n, (ArithmeticFunction.moebius k : ℝ) / (k : ℝ)

/-- Generalized harmonic numbers `H_n^(p)`. -/
def harmonic (n p : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (1 : ℕ) n, (((k : ℝ) ^ p)⁻¹)

/-- The positive head contribution obtained from the exact positive Hardy series
by substituting `R_n(j) = j A_n` for `j ≤ n`. -/
def positiveHead (n : ℕ) (α : ℝ) : ℝ :=
  (1 / (2 * α)) *
    ∑ j ∈ Finset.Icc (1 : ℕ) n,
      ((j : ℝ) * mobiusPartial n) ^ 2 *
        (Real.rpow (j : ℝ) (-2 * α) -
          Real.rpow ((j + 1 : ℕ) : ℝ) (-2 * α))

/-- The scale in the subcritical head asymptotic. -/
def positiveHeadScale (n : ℕ) (α : ℝ) : ℝ :=
  mobiusPartial n ^ 2 * Real.rpow (n : ℝ) (2 - 2 * α) / (2 - 2 * α)

/-- The exact scalar factor at `α = 1`. -/
def positiveHeadOneScalar (n : ℕ) : ℝ :=
  harmonic (n + 1) 1 - (1 / 2 : ℝ) * harmonic (n + 1) 2 - (1 / 2 : ℝ)

/-- Exact and asymptotic positive head size from admitted Claim 10277. -/
def claim10277 : Prop :=
  (∀ α : ℝ, 0 < α → α < 1 →
    Asymptotics.IsEquivalent Filter.atTop
      (fun n : ℕ => positiveHead n α)
      (fun n : ℕ => positiveHeadScale n α)) ∧
  (∀ n : ℕ,
    positiveHead n 1 = mobiusPartial n ^ 2 * positiveHeadOneScalar n) ∧
  Asymptotics.IsBigO Filter.atTop
    (fun n : ℕ => positiveHeadOneScalar n - Real.log (n : ℝ))
    (fun _ : ℕ => (1 : ℝ))

end

end MathlibPlus.Open.Analysis.Claim10277
