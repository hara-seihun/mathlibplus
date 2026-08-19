import MathlibPlus.Open.ResearchFormalization.O0356.FirstPairExteriorSquare15677

open MeasureTheory
open scoped BigOperators Topology

namespace MathlibPlus.Open.ResearchFormalization.R2632.Claim42982

noncomputable section

open MathlibPlus.Open.ResearchFormalization.O0356.Claim15677

private noncomputable def besselJ42982 (j : ℕ) (y : ℝ) : ℝ :=
  ∑' k : ℕ,
    ((-1 : ℝ) ^ k * (y / 2) ^ (2 * k + j)) /
      ((Nat.factorial k : ℝ) * (Nat.factorial (j + k) : ℝ))

noncomputable def derivativeKernel42982 (r : ℕ) (x t : ℝ) : ℝ :=
  (-1 : ℝ) ^ (r - 1) *
    Real.rpow (t / x) (((r - 1 : ℕ) : ℝ) / 2) *
      besselJ42982 (r - 1) (2 * Real.sqrt (x * t))

noncomputable def derivative42982
    (S_f : ℕ → ℂ) (x : ℝ) (r : ℕ) : ℂ :=
  iteratedDeriv r (fun z : ℂ => poissonTransform S_f z) (x : ℂ)

noncomputable def centeredNaturalIntegral42982
    (x : ℝ) (r X : ℕ) : ℂ :=
  (∑ m ∈ Finset.Icc 1 X,
    ((ArithmeticFunction.vonMangoldt m : ℝ) / (m : ℝ) : ℂ) *
      (derivativeKernel42982 r x (Real.log (m : ℝ)) : ℂ)) -
    ∫ t in Set.Icc (0 : ℝ) (Real.log (X : ℝ)),
      (derivativeKernel42982 r x t : ℂ)

def naturalOrderRepresentation42982 (S_f : ℕ → ℂ) : Prop :=
  IsHadamardLiCoefficientSequence S_f ∧
    ∀ (x : ℝ), 0 < x → ∀ r : ℕ, 1 ≤ r →
      Filter.Tendsto
        (fun X : ℕ => centeredNaturalIntegral42982 x r X)
        Filter.atTop
        (𝓝 (derivative42982 S_f x r))

def poissonCharlierRepresentation42982 (S_f : ℕ → ℂ) : Prop :=
  naturalOrderRepresentation42982 S_f

noncomputable def literalPrimeRange42982 (T : ℝ) : Finset ℕ :=
  Finset.Icc 1 (Nat.floor (Real.exp T))

noncomputable def literalPrimeTruncation42982
    (x T : ℝ) (r : ℕ) : ℂ :=
  (∑ m ∈ literalPrimeRange42982 T,
    ((ArithmeticFunction.vonMangoldt m : ℝ) / (m : ℝ) : ℂ) *
      (derivativeKernel42982 r x (Real.log (m : ℝ)) : ℂ)) +
    (derivativeKernel42982 (r + 1) x T : ℂ)

noncomputable def uniformDerivativeErrorSup42982
    (S_f : ℕ → ℂ) (A C x : ℝ) : ℝ :=
  sSup {y : ℝ |
    y = 0 ∨ ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ A * x ∧
      y = ‖derivative42982 S_f x r -
        literalPrimeTruncation42982 x
          (C * Real.rpow x (5 / 3 : ℝ) * (Real.log x) ^ 2) r‖}

/-- The fixed Poisson--Charlier carrier has the uniform literal-prime
cutoff estimate with the endpoint derivative kernel retained. -/
def claim_42982 : Prop :=
  ∀ (S_f : ℕ → ℂ),
    poissonCharlierRepresentation42982 S_f →
      ∀ (A H : ℝ), 0 < A → 0 < H →
        ∃ C : ℝ, 0 < C ∧
          ∀ᶠ x : ℝ in Filter.atTop,
            uniformDerivativeErrorSup42982 S_f A C x ≤
              Real.exp (-H * x * Real.log x)

end

end MathlibPlus.Open.ResearchFormalization.R2632.Claim42982
