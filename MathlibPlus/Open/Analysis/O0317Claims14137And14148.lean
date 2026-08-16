import Mathlib
import MathlibPlus.Analysis.Claim14134

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Analysis.O0317

noncomputable section

/-- The Baez--Duarte coefficient sequence in its finite binomial form. -/
noncomputable def baezDuarteCoefficient (k : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (k + 1),
    ((-1 : ℂ) ^ j) * (Nat.choose k j : ℂ) /
      riemannZeta ((2 * j + 2 : ℕ) : ℂ)

/-- The Newton basis polynomial `P_k(z) = prod_{r=1}^k (1-z/r)`. -/
noncomputable def newtonPochhammer (k : ℕ) (z : ℂ) : ℂ :=
  Finset.prod (Finset.range k) (fun r =>
    1 - z / ((r + 1 : ℕ) : ℂ))

/-- The exact weighted dyadic energy from the admitted Baez--Duarte carrier. -/
noncomputable def dyadicEnergy (N : ℕ) : ℝ :=
  MathlibPlus.Analysis.Claim14134.dyadicSquareEnergy
    (fun k => baezDuarteCoefficient k) N

/-- The absolute-value sum on one dyadic Newton block. -/
noncomputable def dyadicBlockNormSum (N : ℕ) (s : ℂ) : ℝ :=
  ∑ k ∈ Finset.Ico N (2 * N),
    ‖baezDuarteCoefficient k * newtonPochhammer k (s / 2)‖

/-- The infimum of the real parts on a compact spectral set. -/
noncomputable def compactInfRealPart (K : Set ℂ) : ℝ :=
  sInf ((fun s : ℂ => s.re) '' K)

/-- The summability scale supplied by the dyadic block estimate. -/
noncomputable def dyadicMajorant (K : Set ℂ) (ε C : ℝ) (j : ℕ) : ℝ :=
  C * Real.rpow ((2 : ℝ) ^ j)
    ((ε + (1 / 2 : ℝ) - compactInfRealPart K) / 2)

/--
Claim 14137.  The energy hypothesis is the weighted
`sum k^(1/2) |c_k|^2`; its Cauchy--Schwarz block estimate has the stated
exponent, with the implied constant chosen before the block index.  Below
the compact real-part margin the resulting dyadic majorant is summable.
-/
def dyadicCauchySchwarzConvergenceEstimate : Prop :=
  ∀ (K : Set ℂ), IsCompact K →
    (∀ s : ℂ, s ∈ K → (1 / 2 : ℝ) < s.re) →
      ∀ ε : ℝ, 0 < ε →
        (∃ C₀ : ℝ, 0 < C₀ ∧
          ∀ M : ℕ, 1 ≤ M →
            dyadicEnergy M ≤ C₀ * Real.rpow (M : ℝ) ε) →
          ∃ C₁ : ℝ, 0 < C₁ ∧
            (∀ N : ℕ, 1 ≤ N → ∀ s : ℂ, s ∈ K →
              dyadicBlockNormSum N s ≤
                C₁ * Real.rpow (N : ℝ)
                  ((ε + (1 / 2 : ℝ) - s.re) / 2)) ∧
            (ε < compactInfRealPart K - (1 / 2 : ℝ) →
              Summable (dyadicMajorant K ε C₁))

/-- Positive integers are the summation carrier in the Riesz channels. -/
def PositiveNat := {n : ℕ // 1 ≤ n}

/-- The exact Mobius channel `A_r(x)`. -/
noncomputable def poissonChannel (r : ℕ) (x : ℝ) : ℝ :=
  ∑' n : PositiveNat,
    (ArithmeticFunction.moebius n.1 : ℝ) /
        (n.1 : ℝ) ^ (2 * r + 2) *
      Real.exp (-x / (n.1 : ℝ) ^ 2)

/-- The original Poissonized Baez--Duarte square. -/
noncomputable def poissonSquare (x : ℝ) : ℝ :=
  Real.exp (-x) *
    ∑' k : ℕ,
      ‖baezDuarteCoefficient k‖ ^ 2 * x ^ k /
        (Nat.factorial k : ℝ)

/-- The channel expansion of the Poisson square. -/
noncomputable def channelSquare (x : ℝ) : ℝ :=
  ∑' r : ℕ,
    x ^ r * (poissonChannel r x) ^ 2 /
      (Nat.factorial r : ℝ)

/-- The classical Riesz function is the zeroth channel multiplied by x. -/
noncomputable def rieszFunction (x : ℝ) : ℝ :=
  x * poissonChannel 0 x

/-- The higher-channel correction to the zeroth Riesz term. -/
noncomputable def higherChannelRemainder (x : ℝ) : ℝ :=
  poissonSquare x - (rieszFunction x) ^ 2 / x ^ 2

/-- The exact positive majorant used for all higher channels. -/
noncomputable def higherChannelMajorant (x : ℝ) : ℝ :=
  x *
    (∑' n : PositiveNat,
      (n.1 : ℝ)⁻¹ ^ 4 *
        Real.exp (-x / (2 * (n.1 : ℝ) ^ 2))) ^ 2

/-- The Poisson window energy on `[N/2,4N]`. -/
noncomputable def poissonWindowEnergy (N : ℕ) : ℝ :=
  ∫ x in Set.Icc ((N : ℝ) / 2) (4 * (N : ℝ)),
    Real.sqrt x * poissonSquare x

/-- The zeroth-channel Riesz local energy on the same window. -/
noncomputable def rieszWindowEnergy (N : ℕ) : ℝ :=
  ∫ x in Set.Icc ((N : ℝ) / 2) (4 * (N : ℝ)),
    (rieszFunction x) ^ 2 /
      Real.rpow x (3 / 2 : ℝ)

/-- The integrated contribution of all channels `r >= 1`. -/
noncomputable def higherChannelWindow (N : ℕ) : ℝ :=
  ∫ x in Set.Icc ((N : ℝ) / 2) (4 * (N : ℝ)),
    Real.sqrt x * higherChannelRemainder x

/-- The `N^(o(1))` bound used for the target and Riesz window energies. -/
def epsilonPowerBound (F : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, 1 ≤ N →
        F N ≤ C * Real.rpow (N : ℝ) ε

/--
Claim 14148.  The positive higher Poisson channels have only the
`N^(-1/2)` integrated scale, while the `N^(o(1))` target is exactly the
zeroth-channel Riesz local-energy target.
-/
def higherChannelsCannotCarryRHScale : Prop :=
  (∀ x : ℝ, poissonSquare x = channelSquare x) ∧
  (∀ x : ℝ, 0 < x →
    poissonSquare x =
      (rieszFunction x) ^ 2 / x ^ 2 +
        ∑' r : ℕ,
          x ^ (r + 1) * (poissonChannel (r + 1) x) ^ 2 /
            (Nat.factorial (r + 1) : ℝ)) ∧
  (∀ x : ℝ, 1 ≤ x →
    0 ≤ higherChannelRemainder x ∧
      higherChannelRemainder x ≤ higherChannelMajorant x) ∧
  (∃ C : ℝ, 0 < C ∧
    ∀ x : ℝ, 1 ≤ x →
      higherChannelRemainder x ≤ C * Real.rpow x (-2 : ℝ)) ∧
  (∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, 1 ≤ N →
      0 ≤ higherChannelWindow N ∧
        higherChannelWindow N ≤ C * Real.rpow (N : ℝ) (-1 / 2 : ℝ)) ∧
  (epsilonPowerBound dyadicEnergy ↔
    epsilonPowerBound poissonWindowEnergy) ∧
  (epsilonPowerBound poissonWindowEnergy ↔
    epsilonPowerBound rieszWindowEnergy)

end

end MathlibPlus.Open.Analysis.O0317
