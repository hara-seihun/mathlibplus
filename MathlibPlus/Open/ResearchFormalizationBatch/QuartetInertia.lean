import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-! Claim 11297: the exact rank-three quartet defect and its inertia. -/

def quartetPPlus (δ T : ℝ) : ℂ :=
  ((δ : ℂ) + Complex.I * (T : ℂ)) ^ 2

def quartetPMinus (δ T : ℝ) : ℂ := starRingEnd ℂ (quartetPPlus δ T)

def quartetUPlus (δ T x : ℝ) : ℂ :=
  (x : ℂ) / ((x : ℂ) ^ 2 - quartetPPlus δ T)

def quartetUMinus (δ T x : ℝ) : ℂ :=
  (x : ℂ) / ((x : ℂ) ^ 2 - quartetPMinus δ T)

def quartetUZero (T x : ℝ) : ℝ :=
  x / (x ^ 2 + T ^ 2)

def quartetRealFeature (δ T : ℝ) (nodes : Fin N → ℝ) : Fin N → ℝ :=
  fun i => (quartetUPlus δ T (nodes i)).re

def quartetImaginaryFeature (δ T : ℝ) (nodes : Fin N → ℝ) : Fin N → ℝ :=
  fun i => (quartetUPlus δ T (nodes i)).im

def quartetZeroFeature (T : ℝ) (nodes : Fin N → ℝ) : Fin N → ℝ :=
  fun i => quartetUZero T (nodes i)

def quartetKernelDefect (δ T : ℝ) (nodes : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    (8 * quartetUPlus δ T (nodes i) * quartetUPlus δ T (nodes j) +
        8 * quartetUMinus δ T (nodes i) * quartetUMinus δ T (nodes j) -
        16 * ((quartetUZero T (nodes i) : ℂ) * quartetUZero T (nodes j))).re

def hasInertia (B : Matrix (Fin N) (Fin N) ℝ)
    (positive negative zeroCount : ℕ) : Prop :=
  ∃ (Q : Matrix (Fin N) (Fin N) ℝ) (d : Fin N → ℝ),
    Matrix.det Q ≠ 0 ∧
      (∀ i, d i = 1 ∨ d i = -1 ∨ d i = 0) ∧
      B = Q * Matrix.diagonal d * Q.transpose ∧
      Fintype.card {i : Fin N // 0 < d i} = positive ∧
      Fintype.card {i : Fin N // d i < 0} = negative ∧
      Fintype.card {i : Fin N // d i = 0} = zeroCount

def matrixRankAtMostThree (B : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  Module.finrank ℝ (LinearMap.range (Matrix.toLin' B)) ≤ 3

def threeQuartetFeaturesIndependent (δ T : ℝ) (nodes : Fin N → ℝ) : Prop :=
  ∀ α β γ : ℝ,
    α • quartetRealFeature δ T nodes +
          β • quartetImaginaryFeature δ T nodes +
          γ • quartetZeroFeature T nodes = 0 →
      α = 0 ∧ β = 0 ∧ γ = 0

def exactQuartetInertia : Prop :=
  ∀ (N : ℕ) (δ T : ℝ) (nodes : Fin N → ℝ),
    3 ≤ N → 0 < δ → 0 < T →
      (∀ i, 0 < nodes i) → Function.Injective nodes →
        threeQuartetFeaturesIndependent δ T nodes ∧
          hasInertia (quartetKernelDefect δ T nodes) 1 2 (N - 3) ∧
          matrixRankAtMostThree (quartetKernelDefect δ T nodes)

end MathlibPlus.Open.ResearchFormalizationBatch
