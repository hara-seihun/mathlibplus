import Mathlib

open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory

namespace MathlibPlus.Open.Analysis.O0355Claim15632

noncomputable section

private abbrev PrimeIndex := {p : ℕ // Nat.Prime p}
private abbrev PositiveNat := {k : ℕ // 1 ≤ k}

private noncomputable def generalizedLambda
    (aY : ℕ → ℕ → ℝ) (Y n : ℕ) : ℝ :=
  if IsPrimePow n then
    (aY Y (Nat.minFac n)) ^ (Nat.factorization n (Nat.minFac n)) *
      Real.log (Nat.minFac n : ℝ)
  else 0

private noncomputable def omegaMass
    (aY : ℕ → ℕ → ℝ) (Y : ℕ)
    (p : PrimeIndex) (k : PositiveNat) : ℝ :=
  ((aY Y p.1) ^ k.1 - 1) * Real.log (p.1 : ℝ) /
    (p.1 : ℝ) ^ k.1

private noncomputable def omegaPositive
    (aY : ℕ → ℕ → ℝ) (Y : ℕ) : Measure ℝ :=
  Measure.sum (fun p : PrimeIndex =>
    Measure.sum (fun k : PositiveNat =>
      ENNReal.ofReal (max (omegaMass aY Y p k) 0) •
        Measure.dirac ((k.1 : ℝ) * Real.log (p.1 : ℝ))))

private noncomputable def omegaNegative
    (aY : ℕ → ℕ → ℝ) (Y : ℕ) : Measure ℝ :=
  Measure.sum (fun p : PrimeIndex =>
    Measure.sum (fun k : PositiveNat =>
      ENNReal.ofReal (max (-(omegaMass aY Y p k)) 0) •
        Measure.dirac ((k.1 : ℝ) * Real.log (p.1 : ℝ))))

private noncomputable def omegaVariationMeasure
    (aY : ℕ → ℕ → ℝ) (Y : ℕ) : Measure ℝ :=
  omegaPositive aY Y + omegaNegative aY Y

private noncomputable def omegaTotalMass
    (aY : ℕ → ℕ → ℝ) (Y : ℕ) : ℝ :=
  ENNReal.toReal (omegaPositive aY Y Set.univ) -
    ENNReal.toReal (omegaNegative aY Y Set.univ)

private noncomputable def naturalDiscrepancySum
    (aY : ℕ → ℕ → ℝ) (Y X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 X,
    (generalizedLambda aY Y n -
      (ArithmeticFunction.vonMangoldt n : ℝ)) / (n : ℝ)

private def correctedPrimeFamily
    (alpha : ℝ) (aY : ℕ → ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
      (∀ p : PrimeIndex, p.1 ≤ Y → aY Y p.1 = 1) ∧
      (∀ p : PrimeIndex, Y < p.1 →
        |aY Y p.1 - 1| ≤ C * Real.rpow (p.1 : ℝ) (-alpha)) ∧
      (∀ n : ℕ, 0 < aY Y n) ∧
      (∀ r s : ℕ, aY Y (r * s) = aY Y r * aY Y s) ∧
      (∑' p : PrimeIndex, ∑' k : PositiveNat,
        omegaMass aY Y p k) = 0

/-- Claim 15632: the exact signed atomic source difference has absolute
summability, total variation `O(Y^-alpha)`, zero total mass, and the natural
ordered prime-power discrepancy limit. -/
def claim15632 : Prop :=
  ∀ (alpha : ℝ) (aY : ℕ → ℕ → ℝ),
    0 < alpha →
      correctedPrimeFamily alpha aY →
        (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ Y : ℕ in atTop,
          Summable (fun p : PrimeIndex =>
            ∑' k : PositiveNat, |omegaMass aY Y p k|) ∧
          ENNReal.toReal
              (omegaVariationMeasure aY Y Set.univ) ≤
            C * Real.rpow (Y : ℝ) (-alpha) ∧
          omegaTotalMass aY Y = 0 ∧
          Tendsto (fun X : ℕ => naturalDiscrepancySum aY Y X)
            atTop (𝓝 0)) ∧
        (∀ᶠ Y : ℕ in atTop,
          ∀ p : PrimeIndex, ∀ k : PositiveNat,
          generalizedLambda aY Y (p.1 ^ k.1) =
            (aY Y p.1) ^ k.1 * Real.log (p.1 : ℝ) ∧
          ArithmeticFunction.vonMangoldt (p.1 ^ k.1) =
            Real.log (p.1 : ℝ) ∧
          omegaMass aY Y p k =
            (generalizedLambda aY Y (p.1 ^ k.1) -
              (ArithmeticFunction.vonMangoldt (p.1 ^ k.1) : ℝ)) /
              ((p.1 ^ k.1 : ℕ) : ℝ))

end

end MathlibPlus.Open.Analysis.O0355Claim15632
