import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Algebra.Claim25931

noncomputable section

/-- The finite fixed-total composition carrier on the interval
`{0, ..., N}`. -/
private def Composition (m N : ℕ) :=
  {μ : Fin m → ℕ // ∑ i, μ i = N}

private def intervalIndex (N t : ℕ) : Fin (N + 1) :=
  Fin.ofNat (N + 1) t

private def subsetFamily (m r : ℕ) : Finset (Finset (Fin m)) :=
  ((Finset.univ : Finset (Fin m)).powerset).filter
    (fun I => I.card = r)

private def subsetIndex {m N : ℕ} (μ : Composition m N)
    (I : Finset (Fin m)) : Fin (N + 1) :=
  intervalIndex N (∑ i ∈ I, μ.1 i)

private def subsetSum {m N : ℕ} (r : ℕ) (l : Fin (N + 1) → ℚ)
    (μ : Composition m N) : ℚ :=
  ∑ I ∈ subsetFamily m r, l (subsetIndex μ I)

/-- The eightfold mixed forward difference at the origin. -/
private def mixedDifference (N : ℕ) (l : Fin (N + 1) → ℚ)
    (μ : Composition 8 N) : ℚ :=
  ∑ I ∈ (Finset.univ : Finset (Fin 8)).powerset,
    (-1 : ℚ) ^ (8 - I.card) * l (subsetIndex μ I)

/-- Reflection on the natural interval. -/
private def reflectionSymmetric (N : ℕ) (l : Fin (N + 1) → ℚ) : Prop :=
  ∀ t : Fin (N + 1),
    l t = l (intervalIndex N (N - t.1))

/-- The residual `M_l = S₄(l)-2S₃(l)+2S₂(l)-2S₁(l)`. -/
private def middleResidual (N : ℕ) (l : Fin (N + 1) → ℚ)
    (μ : Composition 8 N) : ℚ :=
  subsetSum 4 l μ - 2 * subsetSum 3 l μ +
    2 * subsetSum 2 l μ - 2 * subsetSum 1 l μ

/-- The seventh unit forward difference, with its finite-grid domain
explicit. -/
private def unitSeventhDifference (N : ℕ) (l : Fin (N + 1) → ℚ)
    (t : Fin (N + 1)) : Prop :=
  t.1 + 7 ≤ N →
    (∑ j : Fin 8,
      (-1 : ℚ) ^ (7 - j.1) * (Nat.choose 7 j.1 : ℚ) *
        l (intervalIndex N (t.1 + j.1))) = 0

private def unitSeventhDifferenceZero (N : ℕ)
    (l : Fin (N + 1) → ℚ) : Prop :=
  ∀ t : Fin (N + 1), unitSeventhDifference N l t

/-- A function on the finite interval is cubic in the reflection coordinate
`z=t(N-t)`.  This is the exact degree-at-most-six normal form. -/
private def cubicInReflectionCoordinate (N : ℕ)
    (l : Fin (N + 1) → ℚ) : Prop :=
  ∃ d₀ d₁ d₂ d₃ : ℚ,
    ∀ t : Fin (N + 1),
      l t = d₀ + d₁ * ((t.1 : ℚ) * ((N - t.1 : ℕ) : ℚ)) +
        d₂ * ((t.1 : ℚ) * ((N - t.1 : ℕ) : ℚ)) ^ 2 +
        d₃ * ((t.1 : ℚ) * ((N - t.1 : ℕ) : ℚ)) ^ 3

/-- The residual identity attached to the eightfold mixed difference. -/
private def residualIdentity (N : ℕ) (l : Fin (N + 1) → ℚ) : Prop :=
  ∀ μ : Composition 8 N,
    mixedDifference N l μ = 0 ∧
      middleResidual N l μ = -2 * l (intervalIndex N 0)

/-- Claim 25931: on the exact finite fixed-total carrier, reflection symmetry
and vanishing eightfold mixed differences force the seventh unit difference to
vanish and give the cubic-in-`t(N-t)` degree-six normal form; conversely every
such normal form has the vanishing mixed differences and the residual identity.
All finite-difference conclusions are restricted to the interval. -/
def symmetricSexticMiddleClassification_claim25931 : Prop :=
  ∀ N : ℕ, 8 ≤ N →
    ∀ l : Fin (N + 1) → ℚ,
      reflectionSymmetric N l →
        ((∀ μ : Composition 8 N, mixedDifference N l μ = 0) →
          unitSeventhDifferenceZero N l ∧
            cubicInReflectionCoordinate N l) ∧
        (cubicInReflectionCoordinate N l → residualIdentity N l)

end

end MathlibPlus.Open.Algebra.Claim25931
