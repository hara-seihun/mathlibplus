import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

noncomputable def simpleZetaZero (ρ : ℂ) : Prop :=
  riemannZeta ρ = 0 ∧ deriv riemannZeta ρ ≠ 0

noncomputable def inverseMellinResiduePacket (ρ s : ℂ) (u : ℝ) : ℂ :=
  Complex.Gamma (ρ - s) * Complex.cpow (u : ℂ) (s - ρ) /
    deriv riemannZeta ρ

noncomputable def nymanGammaPacket (ρ : ℂ) (W : ℂ → ℂ) (t : ℝ) : ℂ :=
  riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) *
      W (ρ - ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) /
    ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)

noncomputable def nymanGammaResiduePacket (ρ c : ℂ) (t : ℝ) : ℂ :=
  c * riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) *
      Complex.Gamma (ρ - ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) /
    ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)

def simpleZetaZerosCreateFixedWidthGammaResiduePackets : Prop :=
  (∀ (ρ s : ℂ) (u : ℝ),
    0 < u →
    simpleZetaZero ρ →
    Filter.Tendsto
      (fun w : ℂ =>
        (w - (ρ - s)) * Complex.Gamma w *
          Complex.cpow (u : ℂ) (-w) /
            riemannZeta (s + w))
      (nhdsWithin (ρ - s) {ρ - s}ᶜ)
      (nhds (inverseMellinResiduePacket ρ s u))) ∧
  (∀ (γ : ℝ) (W : ℂ → ℂ),
    let ρ : ℂ := (1 / 2 : ℂ) + (γ : ℂ) * Complex.I
    ContDiff ℂ ⊤ W →
    W ≠ 0 →
    simpleZetaZero ρ →
    MeasureTheory.MemLp (nymanGammaPacket ρ W) 2
      (MeasureTheory.Measure.withDensity MeasureTheory.MeasureSpace.volume
        (fun _ : ℝ => ENNReal.ofReal (1 / (2 * Real.pi)))) ∧
    nymanGammaPacket ρ W ≠ 0 ∧
    ∀ c : ℂ, c ≠ 0 →
      Filter.Tendsto (nymanGammaResiduePacket ρ c)
        (nhdsWithin γ {γ}ᶜ)
        (nhds (-c * deriv riemannZeta ρ / ρ)))

noncomputable def mobiusReal (n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius.toFun n : ℝ)

noncomputable def nymanGenerator (n : ℕ) (t : ℝ) : ℝ :=
  (Int.floor (t / (n : ℝ)) : ℝ) - (Int.floor t : ℝ) / (n : ℝ)

noncomputable def exponentialNymanApproximant (u t : ℝ) : ℝ :=
  ∑' n : ℕ,
    if 0 < n then
      mobiusReal n * Real.exp (-((n : ℝ) * u)) * nymanGenerator n t
    else 0

noncomputable def integerError (k : ℕ) (x : ℝ) : ℝ :=
  exponentialNymanApproximant (-Real.log x) (k : ℝ) - 1

noncomputable def divisorCoefficient (j : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ j.divisors, mobiusReal n * x ^ n

noncomputable def mobiusDampingSum (x : ℝ) : ℝ :=
  ∑' n : ℕ,
    if 0 < n then mobiusReal n * x ^ n / (n : ℝ) else 0

def incrementIdentityAndDivisorCutoffMeanSquare : Prop :=
  (∀ (u : ℝ) (k : ℕ),
    0 < u →
    1 ≤ k →
    integerError k (Real.exp (-u)) - integerError (k - 1) (Real.exp (-u)) =
      divisorCoefficient k (Real.exp (-u)) - mobiusDampingSum (Real.exp (-u))) ∧
  (∀ X : ℕ,
    1 ≤ X →
    Filter.Tendsto
      (fun K : ℕ =>
        (1 / (K : ℝ)) *
          ∑ k ∈ Finset.Icc (1 : ℕ) K,
            |∑ d ∈ (Finset.Icc (1 : ℕ) X).filter (fun d => d ∣ k), mobiusReal d| ^ 2)
      Filter.atTop
      (nhds (∑ d ∈ Finset.Icc (1 : ℕ) X,
        ∑ e ∈ Finset.Icc (1 : ℕ) X,
          mobiusReal d * mobiusReal e / (Nat.lcm d e : ℝ))))

end MathlibPlus.Open.Analysis
