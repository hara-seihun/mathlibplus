import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Batch01

noncomputable section

/-- Hamming distance and even vectors in the binary `k`-cube. -/
def binaryHammingDistance (k : ℕ) (x y : Fin k → Bool) : ℕ :=
  (Finset.univ.filter (fun i => x i ≠ y i)).card

def evenBinaryVector (k : ℕ) (x : Fin k → Bool) : Prop :=
  (Finset.univ.filter (fun i => x i)).card % 2 = 0

def evenDistanceFourSet (k : ℕ) (S : Finset (Fin k → Bool)) : Prop :=
  (∀ x ∈ S, evenBinaryVector k x) ∧
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 4 ≤ binaryHammingDistance k x y

noncomputable def A_even (k : ℕ) : ℕ := by
  classical
  let admissible := Finset.univ.filter (evenDistanceFourSet k)
  have h : admissible.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [admissible, evenDistanceFourSet]
  exact admissible.sup' h Finset.card

def alpha (k : ℕ) : ℝ :=
  (A_even k : ℝ) / (2 : ℝ) ^ (k - 1)

/-- `A_even(k,4)` is the largest admissible even-code cardinality, with its
 normalized density. -/
def claim35794 : Prop :=
  ∀ k : ℕ,
    IsGreatest
      {m : ℕ | ∃ S : Finset (Fin k → Bool),
        evenDistanceFourSet k S ∧ S.card = m}
      (A_even k) ∧
      alpha k = (A_even k : ℝ) / (2 : ℝ) ^ (k - 1)

def codingRank (k : ℕ) : ℕ := Nat.succ (Nat.clog 2 k)

def parityCheckMatrix (k : ℕ)
    (v : Fin k → (Fin (codingRank k - 1) → ZMod 2)) :
    Matrix (Fin (codingRank k)) (Fin k) (ZMod 2) :=
  fun i j => Fin.cases 1 (fun h => v j h) i

def binaryWeight {k : ℕ} (x : Fin k → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun i => x i ≠ 0)).card

def evenZModVector {k : ℕ} (x : Fin k → ZMod 2) : Prop :=
  (∑ i, x i) = 0

def parityKernel (k : ℕ)
    (v : Fin k → (Fin (codingRank k - 1) → ZMod 2)) :
    Set (Fin k → ZMod 2) :=
  {x | Matrix.mulVec (parityCheckMatrix k v) x = 0}

/-- The parity-check construction with distinct columns and the stated
 density lower bound. -/
def claim35798 : Prop :=
  ∀ k : ℕ, 5 ≤ k →
    (∃ v : Fin k → (Fin (codingRank k - 1) → ZMod 2),
      Function.Injective v ∧
        (∀ x : Fin k → ZMod 2, x ∈ parityKernel k v → evenZModVector x) ∧
        (∀ x : Fin k → ZMod 2,
          x ∈ parityKernel k v → x ≠ 0 → 4 ≤ binaryWeight x)) ∧
      alpha k ≥ (2 : ℝ) ^ ((1 : ℤ) - (codingRank k : ℤ)) ∧
      (2 : ℝ) ^ (-(Nat.clog 2 k : ℤ)) ≥ 1 / (2 * k : ℝ)

end
end MathlibPlus.Open.ResearchFormalization.Batch01
