import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch_01a001bb_9953_7035_bfdc_d3409ee54f8a

/-- Exact endpoint-integral form of the dyadic layer, with the odd-square shell
    definitions and normalization supplied by the admitted repair context. -/
def exactEndpointIntegralDyadicLayer : Prop :=
  let OddNat : Type := {m : ℕ // Odd m}
  let q : ℝ := Real.rpow 2 (-(1 : ℝ) / 2)
  let alpha : OddNat → ℝ := fun m => Real.pi * (m : ℝ) ^ 2
  let T : OddNat → ℕ → ℝ := fun m k => alpha m * (4 : ℝ) ^ k
  let phi : OddNat → ℝ → ℝ := fun m u =>
    (4 * Real.pi ^ 2 * (m : ℝ) ^ 4 * Real.exp (9 * u / 2) -
        6 * Real.pi * (m : ℝ) ^ 2 * Real.exp (5 * u / 2)) *
      Real.exp (-Real.pi * (m : ℝ) ^ 2 * Real.exp (2 * u))
  let I : OddNat → ℕ → ℝ → ℝ := fun m k s =>
    ∫ v in Set.Ioi ((k : ℝ) * Real.log 2),
      phi m v * Real.exp (s * (v - (k : ℝ) * Real.log 2))
  let g : ℕ → ℝ → ℝ := fun k r =>
    Real.rpow 2 (-((k : ℝ) / 2)) *
      ∑' m : OddNat, (I m k r + I m k (-r))
  ∀ (k : ℕ) (r : ℝ),
    g k r =
      2 * q ^ k *
        ∑' m : OddNat,
          Real.rpow (alpha m) (-(1 : ℝ) / 4) *
            ∫ t in Set.Ioi (T m k),
              Real.exp (-t) *
                (2 * Real.rpow t ((5 : ℝ) / 4) -
                  3 * Real.rpow t ((1 : ℝ) / 4)) *
                Real.cosh ((r / 2) * Real.log (t / T m k))

/-- The signed Hermite quadrature error has the positive Peano kernel
    F(r) = {r}/r^3.  The representation is the result of two radial
    integrations by parts, rather than termwise positivity of shell charges. -/
def positivePeanoKernelInterpretation : Prop :=
  let F : ℝ → ℝ := fun r => Int.fract r / r ^ 3
  let Test : (ℝ → ℝ) → Prop := fun φ =>
    ContDiff ℝ ⊤ φ ∧ HasCompactSupport φ
  let error : (ℝ → ℝ) → ℝ := fun φ =>
    (-2 : ℝ) * (∫ r in Set.Ioi (0 : ℝ), φ r) +
      ∑' n : {n : ℕ // 0 < n},
        (3 * φ (n : ℝ) + (n : ℝ) * deriv φ (n : ℝ))
  (∀ r : ℝ, 0 < r → 0 ≤ F r) ∧
    ∀ φ : ℝ → ℝ, Test φ →
      error φ =
        ∫ r in Set.Ioi (0 : ℝ),
          F r * deriv (fun x : ℝ => x ^ 4 * deriv φ x) r

end MathlibPlus.Open.ResearchFormalizationBatch_01a001bb_9953_7035_bfdc_d3409ee54f8a
