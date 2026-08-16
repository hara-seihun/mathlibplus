import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research

abbrev Two := Fin 2
abbrev FourIndex := Two × Two
abbrev FourMatrix := Matrix FourIndex FourIndex ℂ

noncomputable def pauliI : Matrix Two Two ℂ := !![1, 0; 0, 1]
noncomputable def pauliX : Matrix Two Two ℂ := !![0, 1; 1, 0]
noncomputable def pauliY : Matrix Two Two ℂ := !![0, -Complex.I; Complex.I, 0]
noncomputable def pauliZ : Matrix Two Two ℂ := !![1, 0; 0, -1]

noncomputable def tensor (A B : Matrix Two Two ℂ) : FourMatrix :=
  fun i j => A i.1 j.1 * B i.2 j.2

noncomputable def fourIdentity : FourMatrix := tensor pauliI pauliI

noncomputable def qVis (x g : ℝ) : FourMatrix :=
  (((2 + x) / 4 : ℝ) : ℂ) • fourIdentity -
    (((1 : ℝ) / 2 : ℝ) : ℂ) • tensor pauliX pauliX -
    (((g / 4 : ℝ) : ℝ) : ℂ) • tensor pauliZ pauliY

noncomputable def nullBasis : Fin 7 → FourMatrix :=
  ![ tensor pauliY pauliI
   , tensor pauliY pauliX
   , tensor pauliY pauliY
   , tensor pauliY pauliZ
   , tensor pauliI pauliZ
   , tensor pauliX pauliZ
   , tensor pauliZ pauliZ ]

noncomputable def nullPerturbation (α : Fin 7 → ℝ) : FourMatrix :=
  (α 0 : ℂ) • nullBasis 0 +
    (α 1 : ℂ) • nullBasis 1 +
    (α 2 : ℂ) • nullBasis 2 +
    (α 3 : ℂ) • nullBasis 3 +
    (α 4 : ℂ) • nullBasis 4 +
    (α 5 : ℂ) • nullBasis 5 +
    (α 6 : ℂ) • nullBasis 6

noncomputable def partialTranspose (Q : FourMatrix) : FourMatrix :=
  fun i j => Q (i.1, j.2) (j.1, i.2)

noncomputable def frobeniusNormSq (Q : FourMatrix) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (Q i j)

noncomputable def frobeniusInner (A B : FourMatrix) : ℂ :=
  ∑ i, ∑ j, star (A i j) * B i j

noncomputable def vectorNormSq (v : FourIndex → ℂ) : ℝ :=
  ∑ i, Complex.normSq (v i)

noncomputable def rayleigh (Q : FourMatrix) (v : FourIndex → ℂ) : ℝ :=
  (∑ i, ∑ j, (star (v i) * Q i j * v j)).re

noncomputable def lambdaMin (Q : FourMatrix) : ℝ :=
  sInf { r : ℝ | ∃ v : FourIndex → ℂ, vectorNormSq v = 1 ∧ r = rayleigh Q v }

noncomputable def commonMargin (Q : FourMatrix) : ℝ :=
  min (lambdaMin Q) (lambdaMin (partialTranspose Q))

noncomputable def marginDeficit (x g : ℝ) (α : Fin 7 → ℝ) : ℝ :=
  (x - |g|) / 4 - commonMargin (qVis x g + nullPerturbation α)

noncomputable def offEnergy (α : Fin 7 → ℝ) : ℝ :=
  (α 0) ^ 2 + (α 1) ^ 2 + (α 4) ^ 2 + (α 5) ^ 2

noncomputable def diagonalRadius (α : Fin 7 → ℝ) : ℝ :=
  |α 3| + |α 2| + |α 6|

noncomputable def alphaNormSq (α : Fin 7 → ℝ) : ℝ :=
  ∑ i, (α i) ^ 2

noncomputable def alphaNorm (α : Fin 7 → ℝ) : ℝ :=
  Real.sqrt (alphaNormSq α)

noncomputable def psi (L S : ℝ) : ℝ :=
  (Real.sqrt (L ^ 2 + 4 * S) - L) / 2

noncomputable def collapseA (g : ℝ) : ℝ := |g| / 4
noncomputable def collapseL (g : ℝ) : ℝ := 1 + |g| / 2
noncomputable def collapseU (g δ : ℝ) : ℝ :=
  2 * collapseA g * δ + δ ^ 2
noncomputable def collapseB (g δ : ℝ) : ℝ :=
  δ + Real.sqrt (3 * collapseU g δ)
noncomputable def collapseBound (g δ : ℝ) : ℝ :=
  collapseU g δ + collapseB g δ * (collapseL g + collapseB g δ)

noncomputable def claim13513_offBlockCoercivity : Prop :=
  ∀ (x g : ℝ) (α : Fin 7 → ℝ),
    ((α 3 = 0 ∧ α 2 = 0 ∧ α 6 = 0) →
        marginDeficit x g α ≥ psi (collapseL g) (offEnergy α)) ∧
      marginDeficit x g α ≥
        psi (collapseL g) (offEnergy α) - diagonalRadius α

noncomputable def claim13514_quantitativeNearOptimizerCollapse : Prop :=
  (∀ (x g : ℝ) (α : Fin 7 → ℝ) (δ : ℝ),
      marginDeficit x g α ≤ δ →
        (α 3) ^ 2 + (α 2) ^ 2 + (α 6) ^ 2 ≤ collapseU g δ ∧
        |α 3| ≤ δ ∧
        offEnergy α ≤ collapseB g δ * (collapseL g + collapseB g δ) ∧
        alphaNormSq α ≤ collapseBound g δ) ∧
    (∀ g : ℝ,
      Filter.Tendsto (fun δ : ℝ => collapseBound g δ)
        (nhdsWithin 0 (Set.Ici 0)) (nhds 0))

noncomputable def claim13516_radialCommonMarginCoercivity : Prop :=
  (∀ i : Fin 7, Matrix.trace (nullBasis i) = 0) ∧
    (∀ i j : Fin 7, i ≠ j → frobeniusInner (nullBasis i) (nullBasis j) = 0) ∧
    (∀ α : Fin 7 → ℝ,
      frobeniusNormSq (nullPerturbation α) = 4 * alphaNormSq α) ∧
    (∀ (x g : ℝ) (α : Fin 7 → ℝ),
      marginDeficit x g α ≥
        alphaNorm α / Real.sqrt 3 - collapseL g) ∧
    (∀ (x g C : ℝ),
      IsCompact {α : Fin 7 → ℝ | marginDeficit x g α ≤ C})

noncomputable def fullKernelMaximum (x g : ℝ) : Prop :=
  let m₀ : ℝ := (x - |g|) / 4
  let values : Set ℝ :=
    Set.range (fun α : Fin 7 → ℝ =>
      commonMargin (qVis x g + nullPerturbation α))
  IsGreatest values m₀ ∧
    (∀ α : Fin 7 → ℝ,
      commonMargin (qVis x g + nullPerturbation α) = m₀ ↔
        nullPerturbation α = 0)

noncomputable def claim13517_uniqueFullKernelCommonMarginOptimizer : Prop :=
  (∀ (x g : ℝ), fullKernelMaximum x g) ∧
    (∀ (x g : ℝ),
      (x - |g|) / 4 < 0 → fullKernelMaximum x g) ∧
    (∀ (x g : ℝ),
      |g| = x →
        commonMargin (qVis x g) = 0 ∧
          (∀ α : Fin 7 → ℝ,
            commonMargin (qVis x g + nullPerturbation α) = 0 →
              nullPerturbation α = 0))

end MathlibPlus.Open.Research
