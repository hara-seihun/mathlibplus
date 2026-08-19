import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.Analysis.Claim4259

noncomputable def poissonWeight4259 (x : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-x) * x ^ n / (Nat.factorial n : ℝ)

noncomputable def laguerreTwo4259 (k : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    (-1 : ℝ) ^ j * (Nat.choose (k + 2) (k - j) : ℝ) * t ^ j /
      (Nat.factorial j : ℝ)

noncomputable def firstShiftLaguerreVector4259 (n : ℕ) (t : ℝ) : ℝ :=
  if 2 ≤ n then laguerreTwo4259 (n - 2) t else 0

noncomputable def firstShiftLaguerreGraphKernel4259
    (x t s : ℝ) : ℝ :=
  ∑' n : ℕ,
    poissonWeight4259 x n *
      (firstShiftLaguerreVector4259 n t *
          firstShiftLaguerreVector4259 n s +
        firstShiftLaguerreVector4259 (n + 1) t *
          firstShiftLaguerreVector4259 (n + 1) s)

noncomputable def positiveCoefficientBivariate4259
    (P : MvPolynomial (Fin 2) ℝ) : Prop :=
  ∀ m ∈ P.support, 0 < P.coeff m

noncomputable def evaluateBivariate4259
    (P : MvPolynomial (Fin 2) ℝ) (t s : ℝ) : ℝ :=
  MvPolynomial.eval₂ (RingHom.id ℝ)
    (fun i => Fin.cases t (fun _ => s) i) P

noncomputable def h4259 (t s : ℝ) : ℝ :=
  (Real.sqrt t + Real.sqrt s) / 2

noncomputable def jensenGap4259 (t s : ℝ) : ℝ :=
  (Real.rpow t (2 / 3 : ℝ) + Real.rpow s (2 / 3 : ℝ)) / 2 -
    Real.rpow (h4259 t s) (4 / 3 : ℝ)

noncomputable def criticalConstant4259 (x : ℝ) : ℝ :=
  (3 / 2 : ℝ) * Real.rpow x (1 / 3 : ℝ)

def criticallyNormalizedKernelBound_claim4259 : Prop :=
  ∀ x : ℝ, 0 < x →
    ∃ P : MvPolynomial (Fin 2) ℝ,
      positiveCoefficientBivariate4259 P ∧
        ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
          Real.exp
              (-criticalConstant4259 x *
                (Real.rpow t (2 / 3 : ℝ) +
                  Real.rpow s (2 / 3 : ℝ))) *
              |firstShiftLaguerreGraphKernel4259 x t s| ≤
            evaluateBivariate4259 P t s *
              Real.exp
                (-3 * Real.rpow x (1 / 3 : ℝ) * jensenGap4259 t s -
                  2 * Real.rpow x (2 / 3 : ℝ) *
                    Real.rpow (h4259 t s) (2 / 3 : ℝ))

end MathlibPlus.Open.Analysis.Claim4259

end
