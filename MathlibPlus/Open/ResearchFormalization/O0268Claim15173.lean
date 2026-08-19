import Mathlib
import MathlibPlus.Analysis.ReciprocalXi

open Filter Asymptotics
open scoped BigOperators Topology

namespace MathlibPlus.Open.ResearchFormalization.O0268Claim15173

noncomputable section

private def admissibleProfile
    (k : ℕ) (P : ℝ → Polynomial ℂ) (d : ℝ → ℕ)
    (B : ℝ → ℝ) (coeff : ℝ → ℕ → ℂ) : Prop :=
  1 ≤ k ∧
    (∀ L : ℝ, 1 ≤ B L) ∧
    (∀ L : ℝ,
      P L = 1 + ∑ j ∈ Finset.Icc 1 (d L),
        Polynomial.monomial j (coeff L j)) ∧
    (∀ (L : ℝ) (j : ℕ), j ∈ Finset.Icc 1 (d L) →
      ‖coeff L j‖ ≤ (B L) ^ j) ∧
    Tendsto (fun L : ℝ => (B L) ^ k * (d L : ℝ) / L)
      atTop (𝓝 0) ∧
    IsLittleO atTop
      (fun L : ℝ => (d L : ℝ) * Real.log (B L))
      (fun L : ℝ => L)

private noncomputable def xiPlane (z : ℂ) : ℂ :=
  MathlibPlus.Analysis.ReciprocalXi.xi
    ((1 / 2 : ℂ) + Complex.I * z)

private noncomputable def profileValue
    (P : ℝ → Polynomial ℂ) (k : ℕ) (L : ℝ) (z : ℂ) : ℂ :=
  (P L).eval
    (z ^ 2 / (Real.rpow L (1 / (k : ℝ)) : ℂ))

private noncomputable def profileCarrier
    (P : ℝ → Polynomial ℂ) (k : ℕ) (L : ℝ) (z : ℂ) : ℂ :=
  xiPlane z / (2 * (Real.pi : ℂ)) * profileValue P k L z

private noncomputable def diniCarrier (L : ℝ) (z : ℂ) : ℂ :=
  (z * Complex.sin ((L : ℂ) * z) -
      (1 / 2 : ℂ) * Complex.cos ((L : ℂ) * z)) /
    (z ^ 2 + (1 / 4 : ℂ))

private noncomputable def ghatExponentialFactor (L : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * (L : ℂ) * z)

private noncomputable def ghatCarrier (L : ℝ) (z : ℂ) : ℂ :=
  ghatExponentialFactor L z * diniCarrier L z

private noncomputable def amplifiedLeadingDiniCoefficient
    (amplification : ℝ → ℝ) (L : ℝ) : ℝ :=
  -amplification L * Real.exp (-5 * L / 2)

private noncomputable def amplifiedSourceTerm
    (amplification : ℝ → ℝ) (L : ℝ) (z : ℂ) : ℂ :=
  (amplifiedLeadingDiniCoefficient amplification L : ℂ) * diniCarrier L z

private noncomputable def modelFunction
    (k : ℕ) (alpha : ℝ) (amplification : ℝ → ℝ)
    (P : ℝ → Polynomial ℂ) (L : ℝ) (z : ℂ) : ℂ :=
  profileCarrier P k L z *
      Complex.exp (-(alpha : ℂ) * z ^ (2 * k)) +
    amplifiedSourceTerm amplification L z

/-- The exponential factor in `ghatCarrier` at the centre height `Im z=1/2`.
It is the carrier normalization, rather than an independent scale. -/
private noncomputable def centerCarrierExponent (L : ℝ) : ℂ :=
  ghatExponentialFactor L (Complex.I / 2)

/-- The actual leading-Dini source magnitude after the centre-carrier
normalization used by `ghatCarrier`. -/
private noncomputable def normalizedCenterSourceCoefficient
    (amplification : ℝ → ℝ) (L : ℝ) : ℂ :=
  -((amplifiedLeadingDiniCoefficient amplification L : ℂ)) /
    centerCarrierExponent L

/-- The normalized source correction as a function of the actual Dini carrier. -/
private noncomputable def normalizedCenterSourceCorrection
    (amplification : ℝ → ℝ) (L : ℝ) (z : ℂ) : ℂ :=
  normalizedCenterSourceCoefficient amplification L * diniCarrier L z

/-- Claim 15173: the negative Dini coefficient, its centre-carrier
normalization, and the exact vanishing criterion are stated for the same
Xi/profile/Dini model as the O-0268 zero-counting carriers. -/
def claim15173 : Prop :=
  ∀ (k : ℕ) (alpha : ℝ) (amplification : ℝ → ℝ)
    (P : ℝ → Polynomial ℂ) (d : ℝ → ℕ)
    (B : ℝ → ℝ) (coeff : ℝ → ℕ → ℂ),
    1 ≤ k →
      0 < alpha →
        admissibleProfile k P d B coeff →
          (∀ L : ℝ, 1 ≤ amplification L) →
            (∀ L : ℝ, ∀ z : ℂ,
              modelFunction k alpha amplification P L z =
                profileCarrier P k L z *
                    Complex.exp (-(alpha : ℂ) * z ^ (2 * k)) +
                  amplifiedSourceTerm amplification L z) ∧
            (∀ L : ℝ,
              amplifiedLeadingDiniCoefficient amplification L =
                -amplification L * Real.exp (-5 * L / 2)) ∧
            (∀ L : ℝ, ∀ z : ℂ,
              normalizedCenterSourceCorrection amplification L z =
                -(amplifiedSourceTerm amplification L z) /
                  centerCarrierExponent L) ∧
            (∀ L : ℝ,
              normalizedCenterSourceCoefficient amplification L =
                (amplification L * Real.exp (-2 * L) : ℝ)) ∧
            ((Tendsto
                (fun L : ℝ => normalizedCenterSourceCoefficient amplification L)
                atTop (𝓝 0)) ↔
              Tendsto
                (fun L : ℝ => (amplification L * Real.exp (-2 * L) : ℂ))
                atTop (𝓝 0))

end

end MathlibPlus.Open.ResearchFormalization.O0268Claim15173
