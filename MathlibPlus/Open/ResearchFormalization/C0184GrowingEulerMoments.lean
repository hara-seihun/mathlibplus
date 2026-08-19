import Mathlib

open Filter MeasureTheory Set Topology Asymptotics
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.C0184

noncomputable section

/-- The Euler order at the logarithmic scale used by C-0184. -/
def eulerOrder (L : ℝ) : ℕ := ⌊L⌋₊

/-- The displayed growing-Euler-order cost at order `r = floor L`. -/
def growingEulerTermCost
    (k : ℕ) (C B L : ℝ) (j : ℕ) : ℝ :=
  B ^ j * Real.rpow L (-((j : ℝ) / (k : ℝ))) *
    Real.rpow
      (C * (((eulerOrder L + j : ℕ) : ℝ)))
      (((eulerOrder L + j : ℕ) : ℝ) / (k : ℝ) + C)

/-- Logarithmic cost relative to the `j = 0` baseline. -/
def growingEulerLogOverhead
    (k : ℕ) (C : ℝ) (B : ℝ → ℝ) (L : ℝ) (j : ℕ) : ℝ :=
  Real.log (growingEulerTermCost k C (B L) L j) -
    Real.log (growingEulerTermCost k C (B L) L 0)

/-- The scale appearing in the C-0184 overhead estimate. -/
def growingEulerOverheadScale
    (B : ℝ → ℝ) (L : ℝ) (j : ℕ) : ℝ :=
  (j : ℝ) * Real.log (B L) + (j : ℝ) +
    (j : ℝ) ^ 2 / (eulerOrder L : ℝ)

/-- The two phase-capacity hypotheses used by the growing profile. -/
def phaseCapacityConditions
    (k : ℕ) (d : ℝ → ℕ) (B : ℝ → ℝ) : Prop :=
  0 < k ∧
    (∀ᶠ L : ℝ in atTop, 1 ≤ L ∧ 1 ≤ B L) ∧
    Tendsto
      (fun L : ℝ => B L ^ k * (d L : ℝ) / L)
      atTop (𝓝 0) ∧
    IsLittleO atTop
      (fun L : ℝ => (d L : ℝ) * Real.log (B L))
      (fun L : ℝ => L)

/-- Claim 2739: at `r = floor L`, the displayed `j`-th cost has the
uniform logarithmic overhead `O(j log B_L + j + j^2/r) = o(L)` for
`j ≤ d_L`. -/
def growingEulerOrderOverhead_claim2739
    (k : ℕ) (d : ℝ → ℕ) (B : ℝ → ℝ) (C : ℝ) : Prop :=
  phaseCapacityConditions k d B ∧
    0 < C ∧
    (∃ K : ℝ, 0 < K ∧
      ∀ᶠ L : ℝ in atTop,
        ∀ j : ℕ, j ≤ d L →
          |growingEulerLogOverhead k C B L j| ≤
            K * growingEulerOverheadScale B L j) ∧
    (∀ ε : ℝ, 0 < ε →
      ∀ᶠ L : ℝ in atTop,
        ∀ j : ℕ, j ≤ d L →
          |growingEulerLogOverhead k C B L j| < ε * L)

/-- The displayed outer-tail exponent. -/
def outerTailExponent
    (k : ℕ) (c C L : ℝ) (j : ℕ) : ℝ :=
  -c * Real.rpow L
      (2 * (k : ℝ) / (2 * (k : ℝ) - 1)) +
    C * (L + (j : ℝ)) * Real.log (L + (j : ℝ))

/-- Claim 2740: the displayed outer-tail exponent tends uniformly to
`-infinity` over `j ≤ d_L` under the stated `d_L = o(L)` and
`d_L log B_L = o(L)` hypotheses. -/
def outerTailReserveSurvives_claim2740
    (k : ℕ) (d : ℝ → ℕ) (B : ℝ → ℝ) (c C : ℝ) : Prop :=
  1 ≤ k ∧
    0 < c ∧
    0 ≤ C ∧
    (∀ᶠ L : ℝ in atTop, 1 ≤ L ∧ 1 ≤ B L) ∧
    IsLittleO atTop
      (fun L : ℝ => (d L : ℝ))
      (fun L : ℝ => L) ∧
    IsLittleO atTop
      (fun L : ℝ => (d L : ℝ) * Real.log (B L))
      (fun L : ℝ => L) ∧
    (∀ M : ℝ, 0 < M →
      ∀ᶠ L : ℝ in atTop,
        ∀ j : ℕ, j ≤ d L →
          outerTailExponent k c C L j < -M)

/-- The center moment and normalized integral carriers in C-0180. -/
def centerMoment (f : ℝ → ℝ) : ℝ := f 0

def normalizedIntegral (f : ℝ → ℝ) : ℝ := ∫ x : ℝ, f x

/-- The Euler operator `D = x d/dx` from C-0180. -/
def eulerD (f : ℝ → ℝ) (x : ℝ) : ℝ := x * deriv f x

/-- The shifted Euler operator `mathcal L = -D(D+1)`. -/
def mathcalL (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => -eulerD (fun y => eulerD f y + f y) x

/-- The shifted operator `mathcal Z = mathcal L - 1/4`. -/
def mathcalZ (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => mathcalL f x - (1 / 4 : ℝ) * f x

/-- A nonconstant shifted-Euler profile term. -/
def shiftedEulerProfileTerm
    (Hαk : ℝ → ℝ) (j : ℕ) : ℝ → ℝ :=
  (mathcalZ^[j]) Hαk

/-- The growing profile carrier `P_L(mathcal Z/L^(1/k)) H_alpha,k`,
with its nonconstant terms written out. -/
def growingProfileCarrier
    (k : ℕ) (Hαk : ℝ → ℝ) (d : ℝ → ℕ)
    (a : ℝ → ℕ → ℝ) (L : ℝ) : ℝ → ℝ :=
  fun x =>
    Hαk x +
      ∑ j ∈ Finset.range (d L),
        (a L (j + 1) /
            Real.rpow L (((j + 1 : ℕ) : ℝ) / (k : ℝ))) *
          shiftedEulerProfileTerm Hαk (j + 1) x

/-- Claim 2741: every nonconstant shifted-Euler term has zero center
and zero normalized integral, and the growing profile therefore leaves
both moment constraints unchanged. -/
def profileTermsPreserveMoments_claim2741
    (k : ℕ) (Hαk : ℝ → ℝ) (d : ℝ → ℕ)
    (a : ℝ → ℕ → ℝ) : Prop :=
  1 ≤ k ∧
    (∀ j : ℕ, 1 ≤ j →
      centerMoment (shiftedEulerProfileTerm Hαk j) = 0 ∧
        normalizedIntegral (shiftedEulerProfileTerm Hαk j) = 0) ∧
    (∀ L : ℝ, 0 < L →
      centerMoment (growingProfileCarrier k Hαk d a L) = centerMoment Hαk ∧
        normalizedIntegral (growingProfileCarrier k Hαk d a L) =
          normalizedIntegral Hαk)

/-- The Dini endpoint contribution from the independent center carrier
`q_lambda`, as in the exact Poisson--Dini split. -/
def centerCarrierDiniContribution
    (q : ℝ → ℝ → ℝ) (lam : ℝ) : ℝ :=
  -q lam 0 / (2 * Real.sqrt lam)

/-- Claim 2742: the unchanged independent center carrier has center
scale `lambda^(-2)`, and its Dini contribution is
`-1/2 lambda^(-5/2) (1+o(1))`. -/
def unchangedLeadingDiniAmplitude_claim2742
    (q : ℝ → ℝ → ℝ) : Prop :=
  Tendsto
      (fun lam : ℝ => q lam 0 / Real.rpow lam (-2 : ℝ))
      atTop (𝓝 1) ∧
    Tendsto
      (fun lam : ℝ =>
        centerCarrierDiniContribution q lam /
          ((-1 / 2 : ℝ) * Real.rpow lam (-5 / 2 : ℝ)))
      atTop (𝓝 1)

end

end MathlibPlus.Open.ResearchFormalization.C0184
