import Mathlib

noncomputable section
open scoped Topology
open Set Filter

namespace MathlibPlus.Open.ResearchFormalizationBatch13782_13785

/-- The prime-square value `1 + p^(2ix) + p^(-2ix)`, written as its real value. -/
def tauPrimeSquare (x : ℝ) (p : ℕ) : ℝ :=
  1 + 2 * Real.cos (2 * x * Real.log (p : ℝ))

/-- The multiplicative square coefficient supplied on the squarefree support. -/
def tauXOnSquare (x : ℝ) (r : ℕ) : ℝ :=
  Finset.prod r.primeFactors (fun p => tauPrimeSquare x p)

/-- The squarefree-support predicate used by the two admitted assertions. -/
def isSquarefree (r : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → ¬ p ^ 2 ∣ r

/-- The coefficient `μ(r) τ_x(r^2)` on the support selected by `μ`. -/
def weightedSquareCoefficient (x : ℝ) (r : ℕ) : ℝ :=
  (ArithmeticFunction.moebius r : ℝ) * tauXOnSquare x (r ^ 2)

/-- The finite set of natural indices `r` with `r ≤ X`. -/
def cutoffRange (X : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (Nat.floor X + 1)).filter (fun r => (r : ℝ) ≤ X)

/-- The cutoff sum over `r ≤ X`. -/
def squareMöbiusCutoffSum (x X : ℝ) : ℝ :=
  Finset.sum (cutoffRange X) (fun r => weightedSquareCoefficient x r)

/-- The number of squarefree integers through the cutoff `X`. -/
def squarefreeCount (X : ℝ) : ℕ := by
  classical
  exact (Finset.filter isSquarefree (cutoffRange X)).card

/--
Compact-height prime-number-theorem cancellation: for every finite height
bound, the square-Möbius cutoff sum has the stated exponentially decaying
uniform bound for all sufficiently large cutoffs.
-/
def claim13782 : Prop :=
  ∀ T : ℝ,
    ∃ cT CT : ℝ,
      0 < cT ∧ 0 < CT ∧
        ∀ᶠ X : ℝ in atTop,
          sSup {y : ℝ |
            ∃ x : ℝ, |x| ≤ T ∧
              y = |squareMöbiusCutoffSum x X|} ≤
            CT * X * Real.exp (-cT * Real.sqrt (Real.log X))

/--
All-height phase alignment, the resulting squarefree lower bound and its
squarefree-count asymptotic, together with failure of any uniform `o(X)`
bound over all real spectral heights.
-/
def claim13785 : Prop :=
  (∀ X : ℝ, ∀ ε : ℝ, 0 < ε →
    ∃ x : ℝ, ∀ r : ℕ, (r : ℝ) ≤ X → isSquarefree r →
      |weightedSquareCoefficient x r - 1| < ε) ∧
  (∀ X : ℝ,
    sSup (Set.range (fun x : ℝ => squareMöbiusCutoffSum x X)) ≥
      (squarefreeCount X : ℝ)) ∧
  (∃ ε : ℝ → ℝ,
    Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ X : ℝ in atTop,
        (squarefreeCount X : ℝ) =
          (6 / (Real.pi ^ 2) + ε X) * X) ∧
  ¬ (∃ ε : ℝ → ℝ,
    Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ X : ℝ in atTop,
        0 ≤ ε X ∧
          sSup {y : ℝ |
            ∃ x : ℝ, y = |squareMöbiusCutoffSum x X|} ≤
            ε X * X)

end MathlibPlus.Open.ResearchFormalizationBatch13782_13785
