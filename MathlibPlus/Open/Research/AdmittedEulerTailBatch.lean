import Mathlib

namespace MathlibPlus.Open.Research

open scoped BigOperators Topology
open Set Filter

noncomputable section

def realPrimePower (p : ℕ) : ℝ :=
  Real.exp (-(3 / 4 : ℝ) * Real.log p)

def rawFiniteEulerProduct (N : ℕ) (w : ℝ) : ℝ :=
  ∏ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)),
    (1 - Real.exp (-w * Real.log p))⁻¹

def omittedLogarithmicTail (N M : ℕ) : ℝ :=
  ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc (N + 1) M),
    -Real.log (1 - realPrimePower p)

def omittedRawTail (N M : ℕ) : ℝ :=
  ∏ p ∈ Finset.filter Nat.Prime (Finset.Icc (N + 1) M),
    (1 - realPrimePower p)⁻¹

/-- Claim 10607. -/
def rawFiniteEulerProductAndOmittedLogTail : Prop :=
  ∀ N M : ℕ,
    rawFiniteEulerProduct N (3 / 4) =
      ∏ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)),
        (1 - Real.exp (-(3 / 4 : ℝ) * Real.log p))⁻¹ ∧
    omittedLogarithmicTail N M =
      ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc (N + 1) M),
        -Real.log (1 - Real.exp (-(3 / 4 : ℝ) * Real.log p))

/-- Claim 10610. -/
def noRawMultiplicativeOrLogarithmicEnclosure : Prop :=
  ∀ N : ℕ,
    Tendsto (fun M : ℕ => omittedLogarithmicTail N M) atTop atTop ∧
    Tendsto (fun M : ℕ => omittedRawTail N M) atTop atTop ∧
    (∀ c : ℝ, 0 < c →
      ¬Tendsto (fun M : ℕ => c * omittedRawTail N M) atTop (𝓝 1)) ∧
    (∀ c : ℝ,
      ¬Tendsto (fun M : ℕ => c + omittedLogarithmicTail N M) atTop (𝓝 0))

end
end MathlibPlus.Open.Research
