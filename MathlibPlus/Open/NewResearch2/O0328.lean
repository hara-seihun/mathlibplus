import Mathlib
import MathlibPlus.Open.Analysis.CenterFlatCompactSourceClaim15459

open MeasureTheory

namespace MathlibPlus.Open.NewResearch2.O0328

noncomputable section

/-- A connected, nondegenerate source interval in the positive half-line. -/
def connectedPositiveSourceInterval (I : Set ℝ) : Prop :=
  I.Nonempty ∧
    IsCompact I ∧
    IsConnected I ∧
    Set.OrdConnected I ∧
    I ⊆ Set.Ioi 0 ∧
    ∃ x ∈ I, ∃ y ∈ I, x < y

/-- A smooth real zero-mean source supported in the given source interval. -/
def smoothZeroMeanSourceOn (I : Set ℝ) (q : ℝ → ℝ) : Prop :=
  ContDiff ℝ ⊤ q ∧
    (∀ x : ℝ, x ∉ I → q x = 0) ∧
    Integrable q ∧
    (∫ x : ℝ, q x) = 0

/-- The Mellin transform on the positive half-line with the source convention
`M_q(s) = ∫₀^∞ q(u) u^(s-1) du`. -/
noncomputable def mellinTransform (q : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ u : ℝ in Set.Ioi 0,
    (q u : ℂ) * Complex.exp ((s - 1) * Complex.log (u : ℂ))

/-- Claim 15469: Mellin evaluation is nontrivial at every point of the open
critical strip for each fixed connected source interval. -/
def claim15469 : Prop :=
  ∀ (I : Set ℝ),
    connectedPositiveSourceInterval I →
    ∀ s₀ : ℂ, 0 < s₀.re → s₀.re < 1 →
      ∃ q : ℝ → ℝ,
        smoothZeroMeanSourceOn I q ∧
          mellinTransform q s₀ ≠ 0

/-- The archimedean Mellin factor `A(s)` from the full carrier. -/
noncomputable def archimedeanFactor (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) *
    Complex.exp (-(s / 2) * Complex.log (Real.pi : ℂ)) *
    Complex.Gamma (s / 2)

/-- The centered coordinate `s(z)=1/2+iz`. -/
def centeredCoordinate (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) + Complex.I * z

/-- The Xi-normalized Mellin multiplier
`E_q(z)=1/2 (M_q(s(z))/A(s(z)) + M_q(1-s(z))/A(1-s(z)))`. -/
noncomputable def xiNormalizedMellinMultiplier
    (q : ℝ → ℝ) (z : ℂ) : ℂ :=
  let s := centeredCoordinate z
  (mellinTransform q s / archimedeanFactor s +
      mellinTransform q (1 - s) / archimedeanFactor (1 - s)) / 2

/-- The completed Xi carrier in the centered variable. -/
noncomputable def xiCarrier : ℂ → ℂ :=
  fun z =>
    archimedeanFactor (centeredCoordinate z) *
      riemannZeta (centeredCoordinate z)

/-- The full Poisson/Mellin carrier `Xi(z) E_q(z)`. -/
noncomputable def fullMellinCarrier
    (q : ℝ → ℝ) (z : ℂ) : ℂ :=
  xiCarrier z * xiNormalizedMellinMultiplier q z

/-- Vanishing of the first `n` complex derivatives at a point. -/
def vanishesToOrderAtLeast
    (f : ℂ → ℂ) (z : ℂ) (n : ℕ) : Prop :=
  ∀ k : ℕ, k < n → iteratedDeriv k f z = 0

/-- Claim 15470: for every fixed nondegenerate center-flat source interval,
the common vanishing orders of all full carriers are exactly those of Xi. -/
def claim15470 : Prop :=
  ∀ z₀ : ℂ,
    0 < (centeredCoordinate z₀).re →
    (centeredCoordinate z₀).re < 1 →
    ∀ a R : ℝ,
      0 < a →
      a < R →
      ∀ n : ℕ,
        ((∀ q : ℝ → ℝ,
            q ∈ MathlibPlus.Open.Analysis.CenterFlatCompactSourceClaim15459.centerFlatSourceClass a R →
              vanishesToOrderAtLeast (fullMellinCarrier q) z₀ n) ↔
          vanishesToOrderAtLeast xiCarrier z₀ n)

end

end MathlibPlus.Open.NewResearch2.O0328
