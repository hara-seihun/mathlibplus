import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research.BatchLinearGrowth

noncomputable section

section ColumnMatroid

variable {𝕜 E R : Type*} [Field 𝕜] [Fintype E] [DecidableEq E] [Fintype R]

/-- The rank of the columns indexed by a finite set. -/
def columnRank (L : Matrix R E 𝕜) (S : Finset E) : ℕ :=
  Module.finrank 𝕜
    (Submodule.span 𝕜 ((fun e : E => (fun r : R => L r e)) '' (S : Set E)))

/-- The finite-set rank conditions for a matroid rank function. -/
def IsMatroidRankFunction (r : Finset E → ℕ) : Prop :=
  r ∅ = 0 ∧
    (∀ S, r S ≤ S.card) ∧
      (∀ S T, S ⊆ T → r S ≤ r T) ∧
        (∀ S T, r (S ∪ T) + r (S ∩ T) ≤ r S + r T)

/-- Claim 5092: the column rank is the rank function of the represented column matroid. -/
def ColumnMatroidRankFunctionClaim (L : Matrix R E 𝕜) (r : Finset E → ℕ) : Prop :=
  (∀ S, r S = columnRank L S) ∧ IsMatroidRankFunction r

end ColumnMatroid

section ObservableProfiles

variable {𝕜 E R : Type*} [Field 𝕜] [Fintype E] [Fintype R]

/-- The stacked observable matrix, with the block index as its first row coordinate. -/
def stackedObservableMatrix (k : ℕ) (φ : E → Fin k → 𝕜) (L : Matrix R E 𝕜) :
    Matrix (Fin k × R) E 𝕜 :=
  fun jr e => φ e jr.1 * L jr.2 e

/-- The coordinate form of the columnwise Khatri--Rao product. -/
def columnwiseKhatriRaoMatrix (k : ℕ) (φ : E → Fin k → 𝕜) (L : Matrix R E 𝕜) :
    Matrix (Fin k × R) E 𝕜 :=
  fun jr e => φ e jr.1 * L jr.2 e

def RowPermutationEquivalent {ι E : Type*} {𝕜 : Type*} [Field 𝕜]
    (A B : Matrix ι E 𝕜) : Prop :=
  ∃ σ : ι ≃ ι, ∀ i e, A (σ i) e = B i e

/-- Claim 5096: a normalized observable profile is, up to row permutation, Khatri--Rao. -/
def FixedObservableProfileKhatriRaoClaim (k : ℕ) (hk : 0 < k)
    (φ : E → Fin k → 𝕜) (L : Matrix R E 𝕜) : Prop :=
  (∀ e, φ e ⟨0, hk⟩ = 1) ∧
    RowPermutationEquivalent (stackedObservableMatrix k φ L)
      (columnwiseKhatriRaoMatrix k φ L)

end ObservableProfiles

section GrowthWords

variable {𝕜 : Type*} [Field 𝕜]

/-- A word of length m, stored with its outermost (last-applied) letter first. -/
inductive Word (k : ℕ) : ℕ → Type
  | nil : Word k 0
  | cons {m : ℕ} (i : Fin k) : Word k m → Word k (m + 1)

variable {V : ℕ → Type*} [∀ n, AddCommGroup (V n)] [∀ n, Module 𝕜 (V n)]

/-- Apply a word from right to left, raising the grade once per letter. -/
def applyWord {k : ℕ} (G : ∀ n, Fin k → V n →ₗ[𝕜] V (n + 1)) :
    {n m : ℕ} → Word k m → V n → V (n + m)
  | n, 0, .nil, v => v
  | n, m + 1, .cons i w, v => G (n + m) i (applyWord G w v)

/-- The span of all length-m words applied to a distinguished vector. -/
def wordSpan {k n₀ m : ℕ} (G : ∀ n, Fin k → V n →ₗ[𝕜] V (n + 1))
    (e : V n₀) : Submodule 𝕜 (V (n₀ + m)) :=
  Submodule.span 𝕜 (Set.range (fun w : Word k m => applyWord G w e))

/-- Claim 5105: the word span at level n₀+m is the span of the degree-m words. -/
def WordSpanRaisingOperatorsClaim {k n₀ : ℕ}
    (G : ∀ n, Fin k → V n →ₗ[𝕜] V (n + 1)) (e : V n₀)
    (W : ∀ n, Submodule 𝕜 (V n)) : Prop :=
  ∀ m, W (n₀ + m) = wordSpan G e

variable {k n₀ m : ℕ}

/-- The coordinate of a vector in a basis at a growth-history word and state. -/
def growthHistoryCoordinate {ι : Type*}
    (B : Module.Basis ι 𝕜 (V (n₀ + m)))
    (G : ∀ n, Fin k → V n →ₗ[𝕜] V (n + 1)) (e : V n₀)
    (w : Word k m) (T : ι) : 𝕜 :=
  (B.repr (applyWord G w e)) T

/-- The growth-history matrix at a fixed level. -/
def growthHistoryMatrix {ι : Type*}
    (B : Module.Basis ι 𝕜 (V (n₀ + m)))
    (G : ∀ n, Fin k → V n →ₗ[𝕜] V (n + 1)) (e : V n₀) :
    Matrix (Word k m) ι 𝕜 :=
  fun w T => growthHistoryCoordinate B G e w T

/-- Claim 5107: the matrix entries are the growth-history coordinates. -/
def GrowthHistoryCoordinatesClaim {ι : Type*}
    (B : Module.Basis ι 𝕜 (V (n₀ + m)))
    (G : ∀ n, Fin k → V n →ₗ[𝕜] V (n + 1)) (e : V n₀)
    (H : Matrix (Word k m) ι 𝕜) : Prop :=
  ∀ w T, H w T = growthHistoryCoordinate B G e w T

/-- Full column rank expressed as linear independence of the column vectors. -/
def HasFullColumnRank {ι κ : Type*} (H : Matrix ι κ 𝕜) : Prop :=
  LinearIndependent 𝕜 (fun j : κ => fun i : ι => H i j)

/-- The growth-alphabet condition in terms of word spans. -/
def IsGrowthAlphabet {k n₀ : ℕ}
    (G : ∀ n, Fin k → V n →ₗ[𝕜] V (n + 1)) (e : V n₀) : Prop :=
  ∀ m, wordSpan G e = (⊤ : Submodule 𝕜 (V (n₀ + m)))

/-- Claim 5108: growth alphabets are exactly full-column-rank history matrices. -/
def GrowthAlphabetIffHistoryFullColumnRankClaim {ι : ℕ → Type*}
    (G : ∀ n, Fin k → V n →ₗ[𝕜] V (n + 1)) (e : V n₀)
    (B : ∀ m, Module.Basis (ι m) 𝕜 (V (n₀ + m))) : Prop :=
  IsGrowthAlphabet G e ↔
    ∀ m, HasFullColumnRank (growthHistoryMatrix (B m) G e)

/-- Pairwise separation of the columns of a matrix. -/
def PairwiseDistinctColumns {ι κ : Type*} (H : Matrix ι κ 𝕜) : Prop :=
  ∀ ⦃j₁ j₂ : κ⦄, j₁ ≠ j₂ → (fun i => H i j₁) ≠ (fun i => H i j₂)

/-- The three signatures (1,0), (0,1), (1,1) as columns of a 2-by-3 matrix. -/
def signatureExample : Matrix (Fin 2) (Fin 3) ℚ :=
  fun i j =>
    if i = 0 ∧ j = 0 then 1 else
      if i = 0 ∧ j = 2 then 1 else
        if i = 1 ∧ j = 1 then 1 else
          if i = 1 ∧ j = 2 then 1 else 0

def matrixColumnSpanRank {ι κ : Type*} (H : Matrix ι κ 𝕜) : ℕ :=
  Module.finrank 𝕜
    (Submodule.span 𝕜 (Set.range (fun j : κ => fun i : ι => H i j)))

/-- Claim 5116: distinct history signatures need not give full column rank. -/
def DistinctSignaturesDoNotImplyCyclicity : Prop :=
  PairwiseDistinctColumns signatureExample ∧
    matrixColumnSpanRank signatureExample = 2 ∧
      ¬ HasFullColumnRank signatureExample

end GrowthWords

end

end MathlibPlus.Open.Research.BatchLinearGrowth
