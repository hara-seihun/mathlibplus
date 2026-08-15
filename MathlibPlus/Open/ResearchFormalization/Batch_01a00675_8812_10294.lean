import Mathlib

open BigOperators
open scoped ArithmeticFunction.Moebius
noncomputable section

namespace MathlibPlus.Open.ResearchFormalization

/-- The per-original-rank Stieltjes rate from the admitted one-hole, leverage,
and packet-decay calculation. -/
def stieltjesRate (y : ℝ) : ℝ :=
  4 * (Real.arcosh (Real.sqrt y / 2) - Real.sqrt (1 - 4 / y))

/-- Positivity, strict increase, and the uniquely located crossing of `log 6`. -/
def stieltjesRateThreshold : Prop :=
  (∀ y : ℝ, 4 < y → 0 < stieltjesRate y) ∧
    (∀ y₁ y₂ : ℝ,
      4 < y₁ → 4 < y₂ → y₁ < y₂ → stieltjesRate y₁ < stieltjesRate y₂) ∧
    (∃! y : ℝ, 4 < y ∧ stieltjesRate y = Real.log 6) ∧
    (∀ y : ℝ,
      4 < y → stieltjesRate y = Real.log 6 →
        (15.8897389717 : ℝ) ≤ y ∧ y < (15.8897389718 : ℝ))

abbrev PositiveNat := {n : ℕ // 0 < n}
abbrev AtLeastTwo := {k : ℕ // 2 ≤ k}

def mobiusCauchyCoefficient (k : ℕ) : ℤ :=
  (Finset.Icc 1 (k - 1)).sum (fun m =>
    ArithmeticFunction.moebius m * ArithmeticFunction.moebius (k - m))

def energyWeight (a : ℝ) (k : ℕ) : ℝ :=
  (Real.exp (-((k : ℝ) * a / Real.exp 1)) -
      Real.exp (-((k : ℝ) * a))) / (k : ℝ)

def mobiusExponentialSum (x : ℝ) : ℝ :=
  ∑' n : PositiveNat,
    (ArithmeticFunction.moebius n.1 : ℝ) * Real.exp (-((n.1 : ℝ) * x))

def cauchyEnergy (a : ℝ) : ℝ :=
  ∑' m : PositiveNat, ∑' n : PositiveNat,
    (ArithmeticFunction.moebius m.1 : ℝ) *
      (ArithmeticFunction.moebius n.1 : ℝ) *
      ((Real.exp (-(((m.1 + n.1 : ℕ) : ℝ) * a / Real.exp 1)) -
          Real.exp (-(((m.1 + n.1 : ℕ) : ℝ) * a))) /
        ((m.1 + n.1 : ℕ) : ℝ))

def exactAdditiveRegrouping (a x : ℝ) : Prop :=
  Summable (fun k : AtLeastTwo =>
      ‖(mobiusCauchyCoefficient k.1 : ℝ) * energyWeight a k.1‖) ∧
    cauchyEnergy a =
      ∑' k : AtLeastTwo,
        (mobiusCauchyCoefficient k.1 : ℝ) * energyWeight a k.1 ∧
    (∑' k : AtLeastTwo,
      (mobiusCauchyCoefficient k.1 : ℝ) *
        Real.exp (-((k.1 : ℝ) * x))) = mobiusExponentialSum x ^ 2

end MathlibPlus.Open.ResearchFormalization
