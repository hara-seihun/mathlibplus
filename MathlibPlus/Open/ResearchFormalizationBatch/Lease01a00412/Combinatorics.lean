import MathlibPlus.LinearAlgebra.LeafExtensionTanner
import MathlibPlus.Open.Combinatorics.MotifStoppingSet

namespace MathlibPlus.Open.Research.FormalizationBatch.Combinatorics

open scoped BigOperators

noncomputable section

/-- Codeword supports are motif stopping sets (Claim 5145). -/
def claim5145 : Prop :=
  ∀ {Card Target Feature Vertex R : Type}
    [CommSemiring R]
    (vertices : Card → Finset Vertex)
    (attach : Card → Vertex → Target)
    (feature : Card → Feature → Vertex → R)
    (a : Target → R),
    a ∈ MathlibPlus.LinearAlgebra.LeafExtensionTanner.dualCommonKernel
      vertices attach feature →
    a ≠ 0 →
      Set.Nonempty (Function.support a) ∧
        MathlibPlus.Open.Combinatorics.MotifStoppingSet.motifStoppingSet
          vertices attach feature (Function.support a)

/-- A complex rising factorial. -/
def complexRising (z : ℂ) (m : ℕ) : ℂ :=
  Finset.prod (Finset.range m) (fun i => z + (i : ℂ))

def alphaPlus (s : ℂ) (k : ℕ) : ℂ := s + (k : ℂ) - 1

def alphaMinus (s : ℂ) (k : ℕ) : ℂ := (k : ℂ) - s

def criticalLine (k : ℕ) (t : ℝ) : ℂ :=
  (1 / 2 : ℂ) + Complex.I * (t : ℂ)

/-- The normalized reflected pivots supplied by the PSS normalization. -/
def normalizedPivotPlus (s : ℂ) (k j : ℕ) : ℂ :=
  (-1 : ℂ) ^ j *
    Complex.exp (((2 : ℂ) - s - 2 * (j : ℂ)) * Real.log 2) *
    (Nat.factorial j : ℂ) *
    complexRising (alphaPlus s k + 1) (j - 1)

def normalizedPivotMinus (s : ℂ) (k j : ℕ) : ℂ :=
  (-1 : ℂ) ^ j *
    Complex.exp (((1 : ℂ) + s - 2 * (j : ℂ)) * Real.log 2) *
    (Nat.factorial j : ℂ) *
    complexRising (alphaMinus s k + 1) (j - 1)

def reflectedPivotProduct (k j : ℕ) (t : ℝ) : ℝ :=
  ((2 : ℝ) ^ ((3 : ℤ) - 4 * (j : ℤ))) *
    (Nat.factorial j : ℝ) ^ 2 *
    ‖complexRising
      (alphaPlus (criticalLine k t) k + 1) (j - 1)‖ ^ 2

/-- Reflected higher pivots pair positively (Claim 7806). -/
def claim7806 : Prop :=
  (∀ (k j : ℕ) (t : ℝ), 1 ≤ j →
    normalizedPivotPlus (criticalLine k t) k j *
        normalizedPivotMinus (criticalLine k t) k j =
      (reflectedPivotProduct k j t : ℂ) ∧
    0 < reflectedPivotProduct k j t) ∧
  (∀ k : ℕ, reflectedPivotProduct k 1 0 = 1 / 2) ∧
  (∀ (k : ℕ) (t : ℝ),
    reflectedPivotProduct k 2 t =
      ((k : ℝ) + 1 / 2) ^ 2 / 8 + t ^ 2 / 8) ∧
  (∀ k : ℕ, ∀ j : ℕ, 2 ≤ j →
    ∃ t₁ t₂ : ℝ,
      reflectedPivotProduct k j t₁ ≠ reflectedPivotProduct k j t₂)

end
end MathlibPlus.Open.Research.FormalizationBatch.Combinatorics
