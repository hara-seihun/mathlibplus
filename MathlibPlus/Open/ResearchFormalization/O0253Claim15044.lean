import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.O0253

open scoped BigOperators Topology
open Filter

/-- The polynomial profile `P_L(u)=1+sum_{j=1}^{d_L} a_{j,L} u^j`. -/
noncomputable def profilePolynomial (d : ℕ) (a : ℕ → ℝ) (u : ℂ) : ℂ :=
  1 + ∑ j ∈ Finset.range d, (a (j + 1) : ℂ) * u ^ (j + 1)

/-- The exact C-0184 admissibility conditions used for the profile sequence. -/
def c0184AdmissibleProfile
    (k : ℕ) (L : ℕ → ℝ) (d : ℕ → ℕ) (B : ℕ → ℝ)
    (a : ℕ → ℕ → ℝ) : Prop :=
  1 ≤ k ∧
    Tendsto L atTop atTop ∧
    (∀ (n j : ℕ), j ∈ Finset.Icc 1 (d n) →
      |a n j| ≤ (B n) ^ j) ∧
    Tendsto
      (fun n => (B n) ^ k * (d n : ℝ) / L n)
      atTop (𝓝 0) ∧
    Tendsto
      (fun n => (d n : ℝ) * Real.log (B n) / L n)
      atTop (𝓝 0)

/-- The restoration estimate supplied by the exact C-0180/C-0184 context. -/
noncomputable def restorationSuperstretched
    (k : ℕ) (L b : ℕ → ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
    ∃ r : ℕ → ℝ,
      Tendsto (fun n => r n / L n) atTop (𝓝 0) ∧
      (∀ᶠ n in atTop,
        |b n| ≤
          Real.exp
            (-c * Real.rpow (L n)
                ((2 * (k : ℝ)) / (2 * (k : ℝ) - 1)) +
              C * L n * Real.log (L n) + r n))

/-- The spectral parameter `s=1/2+iz`. -/
noncomputable def spectralParameter (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) + Complex.I * z

/-- The completed Xi function in the centered spectral variable. -/
noncomputable def centeredXi (z : ℂ) : ℂ :=
  let s := spectralParameter z
  (s * (s - 1) / 2) *
      Complex.cpow (Real.pi : ℂ) (-s / 2) *
      Complex.Gamma (s / 2) * riemannZeta s

/-- The transition scale `T=L^(1/(2k))`. -/
noncomputable def transitionScale (k : ℕ) (L : ℝ) : ℝ :=
  Real.rpow L ((1 : ℝ) / (2 * (k : ℝ)))

/-- The O-0252 transition coordinate `kappa(y)`. -/
noncomputable def kappa (k : ℕ) (α y : ℝ) : ℝ :=
  Real.rpow (((5 / 2 : ℝ) - y) / α)
    ((1 : ℝ) / (2 * (k : ℝ)))

/-- Points on the retained charts/root circles: the fixed positive-height
rectangle, the zero-free factors, and the retained profile floor. -/
def retainedChartOrRootCirclePoint
    (k : ℕ) (α : ℝ) (L : ℕ → ℝ) (d : ℕ → ℕ)
    (a : ℕ → ℕ → ℝ) (y₀ y₁ δ : ℝ) (n : ℕ) (z : ℂ) : Prop :=
  kappa k α y₁ * transitionScale k (L n) ≤ z.re ∧
    z.re ≤ kappa k α y₀ * transitionScale k (L n) ∧
    y₀ - 2 * δ ≤ z.im ∧ z.im ≤ y₁ + 2 * δ ∧
    centeredXi z ≠ 0 ∧
    spectralParameter z * (spectralParameter z - 1) ≠ 0 ∧
    ‖profilePolynomial (d n) (a n)
        (z ^ 2 / (transitionScale k (L n) : ℂ) ^ 2)‖ ≥
      Real.exp (-3 * L n / 4)

/-- The exact main profiled shadow. -/
noncomputable def mainShadow
    (k : ℕ) (α : ℝ) (L : ℕ → ℝ) (d : ℕ → ℕ)
    (a : ℕ → ℕ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  centeredXi z / (2 * (Real.pi : ℂ)) *
    Complex.exp (-(α : ℂ) * z ^ (2 * k)) *
    profilePolynomial (d n) (a n)
      (z ^ 2 / (transitionScale k (L n) : ℂ) ^ 2)

/-- The exact auxiliary R-shadow. -/
noncomputable def rShadow
    (k : ℕ) (α : ℝ) (cαk : ℂ) (z : ℂ) : ℂ :=
  (cαk / 2) * centeredXi z /
      (spectralParameter z * (spectralParameter z - 1)) *
    Complex.exp (-(α : ℂ) * z ^ (2 * k))

/-- The exact auxiliary G-shadow. -/
noncomputable def gShadow
    (k : ℕ) (α : ℝ) (cαk : ℂ) (z : ℂ) : ℂ :=
  cαk * centeredXi z /
      (spectralParameter z * (spectralParameter z - 1)) *
    Complex.exp (-(α : ℂ) * z ^ (2 * k))

/-- The scale displayed in the relative auxiliary estimate, with the fixed
normalization `c_{α,k}` and the `2π` main-shadow factor retained. -/
noncomputable def auxiliaryRelativeScale
    (k : ℕ) (α : ℝ) (cαk : ℂ) (L : ℕ → ℝ) (d : ℕ → ℕ)
    (a : ℕ → ℕ → ℝ) (b : ℕ → ℝ) (n : ℕ) (z : ℂ) : ℝ :=
  2 * Real.pi * ‖cαk‖ *
    ((Real.exp (-2 * L n) + |b n|) /
      ‖spectralParameter z * (spectralParameter z - 1) *
        profilePolynomial (d n) (a n)
          (z ^ 2 / (transitionScale k (L n) : ℂ) ^ 2)‖)

/-- Claim 15044: on the retained O-0252 charts and root circles, the two
rational auxiliary shadows are uniformly `O` of the displayed profile,
with their exact common Xi-superheat carriers and normalization factors,
and are uniformly `o(1)` relative to the main shadow. -/
def rationalAuxiliaryShadowsRelativelyNegligible_claim15044 : Prop :=
  ∀ (k : ℕ) (α : ℝ) (cαk : ℂ)
    (L : ℕ → ℝ) (d : ℕ → ℕ) (B : ℕ → ℝ)
    (a : ℕ → ℕ → ℝ) (b : ℕ → ℝ)
    (y₀ y₁ δ : ℝ),
    0 < α →
    0 < y₀ → y₀ < y₁ → y₁ < 1 / 2 →
    0 < δ → δ < (1 / 2 : ℝ) * min y₀ ((1 / 2 : ℝ) - y₁) →
    c0184AdmissibleProfile k L d B a →
    restorationSuperstretched k L b →
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ᶠ n in atTop, ∀ z : ℂ,
        retainedChartOrRootCirclePoint k α L d a y₀ y₁ δ n z →
          ‖((Real.exp (-2 * L n) : ℂ) *
                rShadow k α cαk z - (b n : ℂ) * gShadow k α cαk z) /
              mainShadow k α L d a n z‖ ≤
            C * auxiliaryRelativeScale k α cαk L d a b n z) ∧
      (∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, ∀ z : ℂ,
          retainedChartOrRootCirclePoint k α L d a y₀ y₁ δ n z →
            ‖((Real.exp (-2 * L n) : ℂ) *
                  rShadow k α cαk z - (b n : ℂ) * gShadow k α cαk z) /
                mainShadow k α L d a n z‖ < ε)

end MathlibPlus.Open.ResearchFormalization.O0253
