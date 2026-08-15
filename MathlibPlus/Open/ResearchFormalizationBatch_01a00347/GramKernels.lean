import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.GramKernels

open MeasureTheory

noncomputable section

/-- The autocorrelation kernel from the admitted even source. -/
def autocorrelationA (w : ℝ → ℝ) (D : ℝ) : ℝ :=
  ∫ v : ℝ, w (v - D) * w (v + D)

/-- The first-Laguerre weighted autocorrelation kernel. -/
def firstLaguerreJ (w : ℝ → ℝ) (D : ℝ) : ℝ :=
  ∫ v : ℝ, v ^ 2 * w (v - D) * w (v + D)

/-- The definitions of `A(D)` and `J(D)` under the stated `L²` hypotheses. -/
def claim7217 : Prop :=
  ∀ w : ℝ → ℝ,
    Even w →
    MemLp w 2 volume →
    MemLp (fun u : ℝ => u * w u) 2 volume →
    ∀ D : ℝ,
      autocorrelationA w D = (∫ v : ℝ, w (v - D) * w (v + D)) ∧
      firstLaguerreJ w D = (∫ v : ℝ, v ^ 2 * w (v - D) * w (v + D))

def translatedSource (w : ℝ → ℝ) (x u : ℝ) : ℝ :=
  w (u - 2 * x)

def centeredPosition (w : ℝ → ℝ) (x u : ℝ) : ℝ :=
  (u - 2 * x) * translatedSource w x u

/-- The translated source and centered position vector have the stated formulas. -/
def claim7218 : Prop :=
  ∀ (w : ℝ → ℝ) (x u : ℝ),
    translatedSource w x u = w (u - 2 * x) ∧
    centeredPosition w x u = (u - 2 * x) * translatedSource w x u

/-- The real `L²` pairing written as its integral representative. -/
def realL2Pairing (f g : ℝ → ℝ) : ℝ :=
  ∫ u : ℝ, f u * g u

/-- The four base Gram identities. -/
def claim7219 : Prop :=
  ∀ (w : ℝ → ℝ),
    Even w →
    MemLp w 2 volume →
    MemLp (fun u : ℝ => u * w u) 2 volume →
    ∀ x x' : ℝ,
      let D := x - x'
      realL2Pairing (translatedSource w x) (translatedSource w x') =
          autocorrelationA w D ∧
      realL2Pairing (translatedSource w x) (centeredPosition w x') =
          D * autocorrelationA w D ∧
      realL2Pairing (centeredPosition w x) (translatedSource w x') =
          -D * autocorrelationA w D ∧
      realL2Pairing (centeredPosition w x) (centeredPosition w x') =
          firstLaguerreJ w D - D ^ 2 * autocorrelationA w D

/-- A real difference kernel is positive definite by all finite Gram tests. -/
def realPositiveDefinite (K : ℝ → ℝ) : Prop :=
  ∀ m : ℕ, ∀ x c : Fin m → ℝ,
    0 ≤ ∑ i : Fin m, ∑ j : Fin m, c i * c j * K (x i - x j)

/-- Positive scalar multiples and the unscaled kernels are positive definite. -/
def claim7224 : Prop :=
  ∀ (w : ℝ → ℝ),
    Even w →
    MemLp w 2 volume →
    MemLp (fun u : ℝ => u * w u) 2 volume →
    ∀ n : ℕ, 0 < n →
      realPositiveDefinite
          (fun D => (n : ℝ) * (autocorrelationA w D) ^ (2 * n - 1) * firstLaguerreJ w D) ∧
      realPositiveDefinite
          (fun D => (autocorrelationA w D) ^ (2 * n - 1) * firstLaguerreJ w D)

end

end MathlibPlus.Open.ResearchFormalization.GramKernels
