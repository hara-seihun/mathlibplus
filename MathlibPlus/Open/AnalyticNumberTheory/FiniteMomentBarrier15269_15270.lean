import Mathlib

open scoped BigOperators Topology

namespace MathlibPlus.Open.AnalyticNumberTheory.FiniteMomentBarrier

noncomputable section

/-- The lower-tail rate used by the sharp-cutoff optimization. -/
def lowerTailRate (u : ℝ) : ℝ :=
  if 0 < u ∧ u < 1 then u - 1 - Real.log u else 0

/-- The natural-index carrier for the finite packet truncated at a real cutoff.
For positive `X`, this is exactly the set of natural indices `1 ≤ n ≤ X`. -/
def cutoffIndices (X : ℝ) : Finset ℕ :=
  Finset.Icc 1 (Nat.floor X)

/-- The sharply truncated von Mangoldt derivative packet from Claim 15259. -/
def packetPolynomial (k : ℕ) (X : ℝ) (s : ℂ) : ℂ :=
  (Nat.factorial (k - 1) : ℂ)⁻¹ *
    ∑ n ∈ cutoffIndices X,
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        (Real.log (n : ℝ) : ℂ) ^ (k - 1) *
        Complex.exp (-s * (Real.log (n : ℝ) : ℂ))

/-- The literal coefficient-square diagonal at the same complex point as the
packet.  The factor `n^(-2 Re(s))` is retained explicitly. -/
def packetDiagonal (k : ℕ) (X : ℝ) (s : ℂ) : ℝ :=
  (Nat.factorial (k - 1) : ℝ)⁻¹ ^ 2 *
    ∑ n ∈ cutoffIndices X,
      (ArithmeticFunction.vonMangoldt n) ^ 2 *
        (Real.log (n : ℝ)) ^ (2 * k - 2) *
        Real.rpow (n : ℝ) (-2 * s.re)

/-- The selected-zero contribution after the logarithmic change of variables.
The displayed integral is the exact `-Γ(k)⁻¹ ∫ y^(k-1)e^(-dy)dy` term. -/
def selectedZeroTerm (k : ℕ) (X d : ℝ) : ℝ :=
  -((Nat.factorial (k - 1) : ℝ)⁻¹) *
    (∫ y in (0 : ℝ)..Real.log X,
      y ^ (k - 1) * Real.exp (-d * y))

/-- The evaluation point `s₀=1+η+iγ`, expressed using `c=η+1/2`. -/
def selectedPoint (c γ : ℝ) : ℂ :=
  ((c + 1 / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I

/-- The sharp exponential cutoff `log X=rk/d`. -/
def sharpCutoff (d r : ℝ) (k : ℕ) : ℝ :=
  Real.exp (r * (k : ℝ) / d)

/-- The selected-zero squared gain over the literal diagonal. -/
def selectedZeroGain (c d r γ : ℝ) (k : ℕ) : ℝ :=
  let X := sharpCutoff d r k
  (|selectedZeroTerm k X d| ^ 2) /
    packetDiagonal k X (selectedPoint c γ)

/-- The exponent of the selected-zero squared gain. -/
def gainExponent (c d r : ℝ) : ℝ :=
  2 * Real.log (c / d) - 2 * lowerTailRate r +
    2 * lowerTailRate (c * r / d)

/-- Claim 15269: every fixed finite moment order has the stated
height-versus-polynomial-length dichotomy for the selected-zero gain. -/
def claim15269 : Prop :=
  ∀ (c d δ r γ : ℝ),
    0 < d →
    0 < δ →
    0 < r →
    d = c - δ →
    2 * δ < 1 →
    ∀ q : ℕ, 1 ≤ q →
      ∀ T : ℕ → ℝ,
        let X : ℕ → ℝ := fun k => sharpCutoff d r k
        let D : ℕ → ℝ := fun k =>
          packetDiagonal k (X k) (selectedPoint c γ)
        let G : ℕ → ℝ := fun k => selectedZeroGain c d r γ k
        let budget : ℕ → ℝ := fun k =>
          (T k + (X k) ^ q) * (D k) ^ q
        (∀ k : ℕ, budget k = (T k + (X k) ^ q) * (D k) ^ q) ∧
          ((∀ᶠ k : ℕ in Filter.atTop, 0 < T k ∧ 0 < D k) →
            ((∀ᶠ k : ℕ in Filter.atTop, (X k) ^ q ≤ T k) →
              Filter.Tendsto (fun k : ℕ => (G k) ^ q / T k)
                Filter.atTop (𝓝 0)) ∧
            ((∀ᶠ k : ℕ in Filter.atTop, T k < (X k) ^ q) →
              Filter.Tendsto (fun k : ℕ => (G k) ^ q / (X k) ^ q)
                Filter.atTop (𝓝 0)))

/-- Claim 15270: the finite Cauchy--Schwarz budget for the exact packet is
followed by the all-sharp-cutoff asymptotic barrier in `2δ<1`. -/
def claim15270 : Prop :=
  (∀ (k X : ℕ),
      2 ≤ k →
        ∀ s : ℂ,
          let active : Finset ℕ :=
            (cutoffIndices (X : ℝ)).filter
              (fun n => ArithmeticFunction.vonMangoldt n ≠ 0)
          let D : ℝ := packetDiagonal k (X : ℝ) s
          let P : ℂ := packetPolynomial k (X : ℝ) s
          ‖P‖ ^ 2 ≤ (active.card : ℝ) * D ∧
            (active.card : ℝ) * D ≤ (X : ℝ) * D) ∧
    ∀ (c d δ r γ : ℝ),
      0 < d →
      0 < δ →
      0 < r →
      d = c - δ →
      2 * δ < 1 →
      let X : ℕ → ℝ := fun k => sharpCutoff d r k
      let G : ℕ → ℝ := fun k => selectedZeroGain c d r γ k
      let E : ℝ := gainExponent c d r
      Filter.Tendsto (fun k : ℕ => G k / X k)
          Filter.atTop (𝓝 0) ∧
        E < r / d

end

end MathlibPlus.Open.AnalyticNumberTheory.FiniteMomentBarrier
