import Mathlib

open MeasureTheory
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R2632.Claim42986

noncomputable section

private noncomputable def besselJ42986 (j : ℕ) (y : ℝ) : ℝ :=
  ∑' k : ℕ,
    ((-1 : ℝ) ^ k * (y / 2) ^ (2 * k + j)) /
      ((Nat.factorial k : ℝ) * (Nat.factorial (j + k) : ℝ))

noncomputable def derivativeKernel42986 (r : ℕ) (x t : ℝ) : ℝ :=
  (-1 : ℝ) ^ (r - 1) *
    Real.rpow (t / x) (((r - 1 : ℕ) : ℝ) / 2) *
      besselJ42986 (r - 1) (2 * Real.sqrt (x * t))

noncomputable def literalPrimeRange42986 (T : ℝ) : Finset ℕ :=
  Finset.Icc 1 (Nat.floor (Real.exp T))

noncomputable def vonMangoldtWeight42986 (m : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt m : ℝ) / (m : ℝ)

noncomputable def finiteChannel42986
    (x T : ℝ) (r : ℕ) : ℝ :=
  (∑ m ∈ literalPrimeRange42986 T,
    vonMangoldtWeight42986 m *
      derivativeKernel42986 r x (Real.log (m : ℝ))) +
    derivativeKernel42986 (r + 1) x T

noncomputable def symmetrizedKernel42986
    (r : ℕ) (x t u : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    (derivativeKernel42986 r x t * derivativeKernel42986 (r + 2) x u +
      derivativeKernel42986 r x u * derivativeKernel42986 (r + 2) x t -
      2 * derivativeKernel42986 (r + 1) x t *
        derivativeKernel42986 (r + 1) x u)

noncomputable def centeredDoubleStieltjesIntegral42986
    (T : ℝ) (φ : ℝ → ℝ → ℝ) : ℝ :=
  let P := literalPrimeRange42986 T
  (∑ m ∈ P, ∑ n ∈ P,
      vonMangoldtWeight42986 m * vonMangoldtWeight42986 n *
        φ (Real.log (m : ℝ)) (Real.log (n : ℝ))) -
    2 * (∑ m ∈ P,
      vonMangoldtWeight42986 m *
        (∫ u in Set.Icc (0 : ℝ) T, φ (Real.log (m : ℝ)) u)) +
    ∫ t in Set.Icc (0 : ℝ) T,
      ∫ u in Set.Icc (0 : ℝ) T, φ t u

noncomputable def finiteDeterminant42986
    (x T : ℝ) (r : ℕ) : ℝ :=
  finiteChannel42986 x T r * finiteChannel42986 x T (r + 2) -
    finiteChannel42986 x T (r + 1) ^ 2

noncomputable def doubleLaplaceSymbol42986
    (r : ℕ) (x : ℝ) (s q : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ),
    ∫ u in Set.Ioi (0 : ℝ),
      Complex.exp (-s * (t : ℂ) - q * (u : ℂ)) *
        (symmetrizedKernel42986 r x t u : ℂ)

noncomputable def antisymmetricSecondDerivative42986
    (r : ℕ) (x t u : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    iteratedDeriv 2
      (fun h : ℝ =>
        derivativeKernel42986 (r + 2) x (t + h) *
          derivativeKernel42986 (r + 2) x (u - h)) 0

def finiteStieltjesIdentity42986 : Prop :=
  ∀ (r : ℕ) (x T : ℝ),
    1 ≤ r → 0 < x → 0 ≤ T →
      finiteDeterminant42986 x T r =
        centeredDoubleStieltjesIntegral42986 T
          (symmetrizedKernel42986 r x)

def doubleLaplaceIdentity42986 : Prop :=
  ∀ (r : ℕ) (x : ℝ) (s q : ℂ),
    1 ≤ r → 0 < x → 0 < s.re → 0 < q.re →
      doubleLaplaceSymbol42986 r x s q =
        ((s - q) ^ 2 /
          (2 * s ^ (r + 2) * q ^ (r + 2))) *
          Complex.exp (-((x : ℂ) * (s⁻¹ + q⁻¹)))

def antisymmetricDifferentialIdentity42986 : Prop :=
  ∀ (r : ℕ) (x t u : ℝ),
    1 ≤ r → 0 < x → 0 ≤ t → 0 ≤ u →
      symmetrizedKernel42986 r x t u =
        antisymmetricSecondDerivative42986 r x t u

/-- The finite determinant remains one coupled centered Stieltjes object; its
kernel has the exact antisymmetric Laplace symbol and differential form. -/
def claim_42986 : Prop :=
  finiteStieltjesIdentity42986 ∧
    doubleLaplaceIdentity42986 ∧
      antisymmetricDifferentialIdentity42986

end

end MathlibPlus.Open.ResearchFormalization.R2632.Claim42986
