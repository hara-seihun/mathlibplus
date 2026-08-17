import Mathlib
import MathlibPlus.Analysis.ReciprocalXi

open Filter Set TopologicalSpace Distribution
open scoped Distributions Topology

namespace MathlibPlus.Open.ResearchFormalization.O0339.CompletedShiftDeltaPrime

noncomputable section

open Classical

/-- The open right half-plane on which the canonical completed-xi logarithm is
chosen. -/
def rightHalfPlane : Set ℂ :=
  {s | 1 < s.re}

/-- The ambient open set for real distributions on the whole line. -/
def realLine : Opens ℝ :=
  ⟨Set.univ, isOpen_univ⟩

/-- The real distributional derivative of the Dirac mass at zero, with the
convention `⟨δ₀',φ⟩ = -φ'(0)`. -/
noncomputable def deltaZeroPrime : 𝓓'(realLine, ℝ) :=
  Distribution.lineDerivCLM (Ω := realLine) (k := ⊤) (n := ⊤) (1 : ℝ)
    (Distribution.delta (Ω := realLine) (n := ⊤) (0 : ℝ))

/-- A pairing of a compactly supported real distribution with a complex
function, defined through real test-function extensions on a neighborhood of
its actual distributional support. -/
def compactDistributionPairingValues
    (T : 𝓓'(realLine, ℝ)) (f : ℝ → ℂ) : Set ℂ :=
  {y |
    ∃ (U : Set ℝ) (φre φim : 𝓓(realLine, ℝ)),
      IsOpen U ∧
        Distribution.dsupport T ⊆ U ∧
          (∀ α : ℝ, α ∈ U →
            φre α = (f α).re ∧ φim α = (f α).im) ∧
            T φre + Complex.I * T φim = y}

/-- A canonical analytic logarithm of the standard completed xi on the
right half-plane, normalized by reality on the positive real axis. -/
def IsCanonicalXiLog (L : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ L rightHalfPlane ∧
    (∀ s : ℂ, s ∈ rightHalfPlane →
      Complex.exp (L s) = MathlibPlus.Analysis.ReciprocalXi.xi s) ∧
      (∀ x : ℝ, 1 < x → (L (x : ℂ)).im = 0)

/-- The shift-variable germ of the canonical logarithm, totalized away from
its domain only so that it can be passed as a function to a test-function
pairing; its values near the distributional support are always on the stated
right-half-plane branch. -/
noncomputable def rightLogShift
    (L : ℂ → ℂ) (s : ℂ) (α : ℝ) : ℂ :=
  if s + (α : ℂ) ∈ rightHalfPlane then
    L (s + (α : ℂ))
  else 0

/-- The delta-prime pairing with the actual canonical logarithmic shift. -/
noncomputable def deltaPrimeShiftLog
    (L : ℂ → ℂ) (s : ℂ) : ℂ :=
  -deriv (fun α : ℝ => rightLogShift L s α) 0

/-- The completed shift obtained by exponentiating the paired `Y_T`. -/
noncomputable def deltaPrimeShiftExp
    (L : ℂ → ℂ) (s : ℂ) : ℂ :=
  Complex.exp (deltaPrimeShiftLog L s)

/-- Absolutely convergent ordinary Dirichlet series with the exact positive
integer carrier and complex coefficients. -/
def absolutelyConvergentOrdinaryDirichletSeries (F : ℂ → ℂ) : Prop :=
  ∃ (a : {n : ℕ // 1 ≤ n} → ℂ) (σ₀ : ℝ),
    (∀ s : ℂ, σ₀ < s.re →
      Summable (fun n : {n : ℕ // 1 ≤ n} =>
        ‖a n * Complex.exp
          (-s * (Real.log (n.1 : ℝ) : ℂ))‖)) ∧
      (∀ s : ℂ, σ₀ < s.re →
        F s = ∑' n : {n : ℕ // 1 ≤ n},
          a n * Complex.exp (-s * (Real.log (n.1 : ℝ) : ℂ)))

/-- Claim 15539: for the concrete `δ₀'` shift and the canonical analytic
right-half-plane logarithm of the standard completed xi, the distributional
pairing is `Y_T=−(log ξ)'` on its full domain, its exponential has the exact
square-root power-law tail, and it is excluded from every absolutely convergent
ordinary Dirichlet series. -/
def claim15539 : Prop :=
  let T : 𝓓'(realLine, ℝ) := deltaZeroPrime
  ∃ L : ℂ → ℂ,
    IsCanonicalXiLog L ∧
      (∀ φ : 𝓓(realLine, ℝ),
        T φ = -((TestFunction.lineDerivCLM ℝ (n := ⊤) (k := ⊤)
          (1 : ℝ) φ) (0 : ℝ))) ∧
        IsCompact (Distribution.dsupport T) ∧
          Distribution.dsupport T ⊆ ({0} : Set ℝ) ∧
            (∀ s : ℂ, s ∈ rightHalfPlane →
              deltaPrimeShiftLog L s ∈
                compactDistributionPairingValues T
                  (rightLogShift L s)) ∧
              (∀ s : ℂ, s ∈ rightHalfPlane →
                deltaPrimeShiftLog L s = -deriv L s) ∧
              Tendsto
                (fun σ : ℝ =>
                  deltaPrimeShiftExp L (σ : ℂ) /
                    (Real.sqrt (2 * Real.pi / σ) : ℂ))
                atTop (𝓝 (1 : ℂ)) ∧
              (¬ ∃ c : ℂ, ∀ᶠ σ : ℝ in atTop,
                deltaPrimeShiftExp L (σ : ℂ) = c) ∧
              ¬ absolutelyConvergentOrdinaryDirichletSeries
                  (deltaPrimeShiftExp L)

end

end MathlibPlus.Open.ResearchFormalization.O0339.CompletedShiftDeltaPrime
