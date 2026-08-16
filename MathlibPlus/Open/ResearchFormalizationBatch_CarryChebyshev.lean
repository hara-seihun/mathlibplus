import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalizationBatch_CarryChebyshev

/-- The unweighted carry transition count for multiplication by `m` in base `b`. -/
def carryTransitionCount (m b : ℕ) (c k : Fin m) : ℕ :=
  (Finset.univ.filter (fun d : Fin b =>
    (m * d.val + c.val) / b = k.val)).card

/-- The normalized carry transition matrix on the actual carry state set
`{0, ..., m - 1}`. -/
def carryMatrix (m b : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  fun c k => (carryTransitionCount m b c k : ℝ) / (b : ℝ)

def P (m b : ℕ) : Matrix (Fin m) (Fin m) ℝ := carryMatrix m b

/-- One-digit uniformity and the resulting power law for every divisible base. -/
def claim10550_oneDigitErasesCarry : Prop :=
  ∀ (m b : ℕ), 2 ≤ m → 2 ≤ b → m ∣ b →
    (∀ (c k : Fin m), P m b c k = (1 : ℝ) / (m : ℝ)) ∧
      (∀ (c₁ c₂ k : Fin m), P m b c₁ k = P m b c₂ k) ∧
      (∀ N : ℕ, 0 < N → (P m b) ^ N = P m b)

/-- A concrete rank-one test: a nonzero matrix whose every two-by-two minor
vanishes.  This is the rank-one condition used below, with no free witness
or callback. -/
def isRankOne {ι κ : Type*} [Nonempty ι] [Nonempty κ]
    (M : Matrix ι κ ℝ) : Prop :=
  (∃ i : ι, ∃ j : κ, M i j ≠ 0) ∧
    ∀ (i₁ i₂ : ι) (j₁ j₂ : κ),
      M i₁ j₁ * M i₂ j₂ = M i₁ j₂ * M i₂ j₁

/-- Tensor synchronization of the actual normalized carry matrices for the
multipliers 2 and 3. -/
def synchronized23 (b : ℕ) : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℝ :=
  fun c k =>
    P 2 b c.1 k.1 * P 3 b c.2 k.2

/-- Tensor synchronization of the actual normalized carry matrices for the
multipliers 2, 3, 5, and 7. -/
def synchronized2357 (b : ℕ) :
    Matrix ((Fin 2 × Fin 3) × (Fin 5 × Fin 7))
      ((Fin 2 × Fin 3) × (Fin 5 × Fin 7)) ℝ :=
  fun c k =>
    P 2 b c.1.1 k.1.1 *
      P 3 b c.1.2 k.1.2 *
      P 5 b c.2.1 k.2.1 *
      P 7 b c.2.2 k.2.2

def uniform23 : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℝ :=
  fun _ _ => (1 : ℝ) / 6

def uniform2357 :
    Matrix ((Fin 2 × Fin 3) × (Fin 5 × Fin 7))
      ((Fin 2 × Fin 3) × (Fin 5 × Fin 7)) ℝ :=
  fun _ _ => (1 : ℝ) / 210

/-- Claim 10555: the prescribed bases and multipliers are the concrete
uniform-projector tensor instances, hence rank one after normalization. -/
def claim10555_prescribedCommonBases : Prop :=
  (2 ∣ 6 ∧ 3 ∣ 6) ∧
    (2 ∣ 12 ∧ 3 ∣ 12) ∧
    (2 ∣ 18 ∧ 3 ∣ 18) ∧
    (2 ∣ 210 ∧ 3 ∣ 210 ∧ 5 ∣ 210 ∧ 7 ∣ 210) ∧
    synchronized23 6 = uniform23 ∧
    synchronized23 12 = uniform23 ∧
    synchronized23 18 = uniform23 ∧
    synchronized2357 210 = uniform2357 ∧
    isRankOne (synchronized23 6) ∧
    isRankOne (synchronized23 12) ∧
    isRankOne (synchronized23 18) ∧
    isRankOne (synchronized2357 210)

end MathlibPlus.Open.ResearchFormalizationBatch_CarryChebyshev

end
