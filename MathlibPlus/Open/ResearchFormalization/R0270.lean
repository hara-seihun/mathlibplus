import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R0270

/-- The planar column k(z) used by the reflection-folding claims. -/
def planarColumn (z : ℝ) : Fin 2 → ℝ :=
  ![1 + z, z ^ 2]

def foldedPlanarColumn (z : ℝ) : Fin 2 → ℝ :=
  planarColumn z + planarColumn (-z)

def sampledUnfolded (j : Fin 4) : Fin 2 → ℝ :=
  planarColumn ((j.1 : ℝ) + 1)

def sampledFolded (j : Fin 4) : Fin 2 → ℝ :=
  foldedPlanarColumn ((j.1 : ℝ) + 1)

/-- The rank-two minor of two labelled columns. -/
def planarMinor (u v : Fin 2 → ℝ) : ℝ :=
  u 0 * v 1 - u 1 * v 0

/-- All six labelled rank-two minors have positive signs. -/
def allPositiveMinors (configuration : Fin 4 → Fin 2 → ℝ) : Prop :=
  ∀ i j : Fin 4, i < j → 0 < planarMinor (configuration i) (configuration j)

/-- The balanced four-column cross-ratio. -/
def balancedCrossRatio (configuration : Fin 4 → Fin 2 → ℝ) : ℝ :=
  (planarMinor (configuration 0) (configuration 2) *
      planarMinor (configuration 1) (configuration 3)) /
    (planarMinor (configuration 0) (configuration 1) *
      planarMinor (configuration 2) (configuration 3))

/-- Positive projective equivalence of labelled columns. -/
def positiveProjectiveEquivalent
    (u v : Fin 4 → Fin 2 → ℝ) : Prop :=
  ∃ A : Matrix (Fin 2) (Fin 2) ℝ,
    Matrix.det A ≠ 0 ∧
    ∃ q : Fin 4 → ℝ,
      (∀ j, 0 < q j) ∧
      ∀ j, Matrix.mulVec A (u j) = q j • v j

/-- Claim 19349: folding preserves the six minor signs but changes the projective modulus. -/
def claim19349 : Prop :=
  allPositiveMinors sampledUnfolded ∧
    allPositiveMinors sampledFolded ∧
    balancedCrossRatio sampledUnfolded = (392 : ℝ) / 95 ∧
    balancedCrossRatio sampledFolded = (32 : ℝ) / 7 ∧
    ¬ positiveProjectiveEquivalent sampledUnfolded sampledFolded

/-- Positive scalar equivalence of individual projective columns. -/
def positiveVectorProjectivelyEquivalent
    (u v : Fin 2 → ℝ) : Prop :=
  ∃ q : ℝ, 0 < q ∧ u = q • v

/-- Claim 19350: a common completion scale is removable, while the relative branch
weight remains as a projective modulus. -/
def claim19350 : Prop :=
  (∀ (z q : ℝ), 0 < q →
      positiveVectorProjectivelyEquivalent (q • planarColumn z) (planarColumn z)) ∧
    ∀ (z qPlus qMinus : ℝ),
      0 < z → 0 < qPlus → 0 < qMinus →
      positiveVectorProjectivelyEquivalent
        (qPlus • planarColumn z + qMinus • planarColumn (-z))
        (planarColumn z + (qMinus / qPlus) • planarColumn (-z)) ∧
      ∀ (rhoOne rhoTwo : ℝ),
        0 < rhoOne → 0 < rhoTwo → rhoOne ≠ rhoTwo →
        ¬ positiveVectorProjectivelyEquivalent
          (planarColumn z + rhoOne • planarColumn (-z))
          (planarColumn z + rhoTwo • planarColumn (-z))

end MathlibPlus.Open.ResearchFormalization.R0270
