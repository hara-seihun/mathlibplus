import Mathlib

namespace MathlibPlus.Open.Analysis.ReciprocalXi

noncomputable def completedXi (s : ℂ) : ℂ :=
  (s * (s - 1) / 2) * completedRiemannZeta s

noncomputable def reciprocalCompletedXi (x : ℝ) : ℝ :=
  (completedXi ((1 / 2 : ℂ) + (x : ℂ))).re

noncomputable def reciprocalCompletedXiFourier (t : ℂ) : ℂ :=
  ∫ x : ℝ,
    Complex.exp (Complex.I * t * (x : ℂ)) /
      (reciprocalCompletedXi x : ℂ)

noncomputable def orientedConfluentDeterminant (m : ℕ) (t : ℂ) : ℂ :=
  (-1 : ℂ) ^ (m * (m - 1) / 2) *
    Matrix.det (fun i j : Fin m =>
      iteratedDeriv (i.val + j.val) reciprocalCompletedXiFourier t)

noncomputable def reciprocalXiVandermonde (m : ℕ) (x : Fin m → ℝ) : ℝ :=
  ∏ i : Fin m, ∏ j : Fin m, if i < j then x j - x i else 1

noncomputable def reciprocalXiWeight (m : ℕ) (x : Fin m → ℝ) : ℝ :=
  (∏ j : Fin m, (reciprocalCompletedXi (x j))⁻¹) *
    (reciprocalXiVandermonde m x) ^ 2

noncomputable def reciprocalXiSumLaw (m : ℕ) : MeasureTheory.Measure ℝ :=
  MeasureTheory.Measure.map (fun x : Fin m → ℝ => ∑ j : Fin m, x j)
    (MeasureTheory.Measure.withDensity
      (MeasureTheory.Measure.pi (fun _ : Fin m =>
        (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure ℝ)))
      (fun x =>
        ENNReal.ofReal
          (reciprocalXiWeight m x /
            (Nat.factorial m : ℝ) /
            (orientedConfluentDeterminant m 0).re)))

noncomputable def reciprocalXiNormalizedDeterminant (m : ℕ) (t : ℂ) : ℂ :=
  orientedConfluentDeterminant m t /
    orientedConfluentDeterminant m 0

noncomputable def reciprocalXiCharacteristic (m : ℕ) (t : ℂ) : ℂ :=
  ∫ y : ℝ, Complex.exp (Complex.I * t * (y : ℂ)) ∂ reciprocalXiSumLaw m

noncomputable def reciprocalXiEvenMoment (m k : ℕ) : ℂ :=
  ∫ y : ℝ, (y : ℂ) ^ (2 * k) ∂ reciprocalXiSumLaw m

noncomputable def reciprocalXiScaledEvenMoment (m k : ℕ) : ℂ :=
  (Nat.factorial k : ℂ) / (Nat.factorial (2 * k) : ℂ) *
    reciprocalXiEvenMoment m k

def claim7112 : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    ∃! H : ℂ → ℂ,
      ∀ t : ℂ,
        H t =
          (-1 : ℂ) ^ (m * (m - 1) / 2) *
            Matrix.det (fun i j : Fin m =>
              iteratedDeriv (i.val + j.val) reciprocalCompletedXiFourier t)

def claim7114 : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    ((orientedConfluentDeterminant m 0).im = 0 ∧
        0 < (orientedConfluentDeterminant m 0).re ∧
        MeasureTheory.IsProbabilityMeasure (reciprocalXiSumLaw m) ∧
        (∀ t : ℂ,
          reciprocalXiNormalizedDeterminant m t =
            reciprocalXiCharacteristic m t) ∧
        (∀ t : ℂ,
          reciprocalXiNormalizedDeterminant m (-t) =
            reciprocalXiNormalizedDeterminant m t) ∧
        AnalyticOnNhd ℂ (reciprocalXiNormalizedDeterminant m) Set.univ) →
      (∀ k : ℕ,
          reciprocalXiScaledEvenMoment m k =
            ((Nat.factorial k : ℂ) * (-1 : ℂ) ^ k *
                iteratedDeriv (2 * k) (orientedConfluentDeterminant m) 0) /
              ((Nat.factorial (2 * k) : ℂ) *
                orientedConfluentDeterminant m 0)) ∧
      ∃! L : ℂ → ℂ,
        AnalyticOnNhd ℂ L Set.univ ∧
          (∀ t : ℂ,
            reciprocalXiNormalizedDeterminant m t = L (t ^ 2)) ∧
          (∀ u : ℂ,
            Summable (fun k : ℕ =>
              ((-1 : ℂ) ^ k * reciprocalXiScaledEvenMoment m k /
                  (Nat.factorial k : ℂ)) * u ^ k) ∧
              L u = ∑' k : ℕ,
                ((-1 : ℂ) ^ k * reciprocalXiScaledEvenMoment m k /
                  (Nat.factorial k : ℂ)) * u ^ k)

end MathlibPlus.Open.Analysis.ReciprocalXi
