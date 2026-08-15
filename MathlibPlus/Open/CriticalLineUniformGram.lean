import Mathlib

open Matrix

namespace MathlibPlus.Open.CriticalLineUniformGram

/-- The matrix `C_c = [[0,-1],[1,-2c]]` from the admitted claim. -/
def companion (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -1; 1, -2 * c]

/-- The one-parameter family forced by invariance. -/
def gram (c a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a, -a * c; -a * c, a]

/-- The spectral condition number of a real symmetric two-by-two matrix.
For a positive-definite symmetric matrix this is the larger eigenvalue divided
by the smaller eigenvalue. -/
noncomputable def spectralConditionNumber
    (G : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  let a := G 0 0
  let b := G 0 1
  let d := G 1 1
  (a + d + Real.sqrt ((a - d) ^ 2 + 4 * b ^ 2)) /
    (a + d - Real.sqrt ((a - d) ^ 2 + 4 * b ^ 2))

/-- A symmetric positive-definite invariant Gram for `companion c`. -/
def IsInvariantGram (c : ℝ) (G : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  Gᵀ = G ∧
    G.PosDef ∧
      (companion c)ᵀ * G * companion c = G

/-- Existence of invariant Grams with one condition-number bound independent
of the index. -/
def HasUniformlyBoundedInvariantGrams {ι : Type*} (c : ι → ℝ) : Prop :=
  ∃ (G : ι → Matrix (Fin 2) (Fin 2) ℝ) (K : ℝ),
    ∀ i, IsInvariantGram (c i) (G i) ∧ spectralConditionNumber (G i) ≤ K

/-- The exact uniform-gap alternative in the admitted claim. -/
def HasUniformStrictParameterGap {ι : Type*} (c : ι → ℝ) : Prop :=
  ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ i, |c i| ≤ ρ

/-- The main equivalence: uniformly bounded invariant Grams exist exactly
when the parameters have a uniform strict gap from the boundary. -/
def uniformlyBoundedInvariantGrams_iff_uniformGap
    {ι : Type*} (c : ι → ℝ) : Prop :=
  HasUniformlyBoundedInvariantGrams c ↔ HasUniformStrictParameterGap c

/-- Invariance and positive definiteness force the displayed one-dimensional
Gram cone, with positive scale and the scale-free condition number. -/
def invariantGramClassification (c : ℝ) : Prop :=
  ∀ G : Matrix (Fin 2) (Fin 2) ℝ,
    IsInvariantGram c G →
      ∃ a : ℝ,
        0 < a ∧
          G = gram c a ∧
            spectralConditionNumber G = (1 + |c|) / (1 - |c|)

/-- The boundary family in the admitted obstruction. -/
noncomputable def boundaryParameter (n : ℕ) : ℝ :=
  1 - 1 / (n + 2 : ℝ)

/-- Pointwise strict local unitarizability for the boundary family, together
with the exact condition number and its unboundedness. -/
def boundaryFamilyObstruction : Prop :=
  (∀ n : ℕ,
    0 ≤ boundaryParameter n ∧
      |boundaryParameter n| < 1 ∧
        IsInvariantGram (boundaryParameter n)
          (gram (boundaryParameter n) 1)) ∧
  (∀ (n : ℕ) (G : Matrix (Fin 2) (Fin 2) ℝ),
    IsInvariantGram (boundaryParameter n) G →
      spectralConditionNumber G = 2 * (n : ℝ) + 3) ∧
  (∀ K : ℝ, ∃ n : ℕ, K < 2 * (n : ℝ) + 3)

/-- Full formal statement of the admitted local-to-uniform obstruction. -/
def criticalLineUniformGramObstruction : Prop :=
  (∀ {ι : Type*} (c : ι → ℝ),
    uniformlyBoundedInvariantGrams_iff_uniformGap c) ∧
  (∀ c : ℝ, invariantGramClassification c) ∧
  boundaryFamilyObstruction

end MathlibPlus.Open.CriticalLineUniformGram
