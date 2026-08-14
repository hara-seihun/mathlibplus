import Mathlib

noncomputable section

open scoped BigOperators

namespace MathlibPlus.Open

def BooleanCube (r : ℕ) := Fin r → Bool

def flipBit {r : ℕ} (ε : BooleanCube r) (j : Fin r) : BooleanCube r :=
  Function.update ε j (Bool.not (ε j))

def BooleanCharacter (r : ℕ) (ε : BooleanCube r) : ℝ :=
  (-1 : ℝ) ^
    (Nat.choose r 2 + ∑ j : Fin r, if ε j = false then j.val else 0)

def NegativeCube (r : ℕ) :=
  {ε : BooleanCube r // BooleanCharacter r ε = (-1 : ℝ)}

def PositiveCube (r : ℕ) :=
  {ε : BooleanCube r // BooleanCharacter r ε = (1 : ℝ)}

noncomputable instance booleanCubeFintype (r : ℕ) : Fintype (BooleanCube r) := by
  unfold BooleanCube
  infer_instance

noncomputable instance negativeCubeFintype (r : ℕ) : Fintype (NegativeCube r) := by
  classical
  unfold NegativeCube
  infer_instance

noncomputable instance positiveCubeFintype (r : ℕ) : Fintype (PositiveCube r) := by
  classical
  unfold PositiveCube
  infer_instance

def EvenInteractionFree {r : ℕ} (B : BooleanCube r → ℝ) : Prop :=
  ∃ n : ℕ, ∃ Bk : Fin n → BooleanCube r → ℝ,
    B = (fun ε => ∑ k : Fin n, Bk k ε) ∧
      ∀ k : Fin n, ∃ j : Fin r,
        Even (j.val + 1) ∧
          ∀ ε : BooleanCube r,
            Bk k (flipBit ε j) = Bk k ε

def RowStochastic {r : ℕ}
    (T : NegativeCube r → PositiveCube r → ℝ) : Prop := by
  classical
  exact ∀ ε : NegativeCube r, ∑ δ : PositiveCube r, T ε δ = 1

def CapacitySlack {r : ℕ} (A : BooleanCube r → ℝ)
    (T : NegativeCube r → PositiveCube r → ℝ)
    (δ : PositiveCube r) : ℝ :=
  A δ.1 - ∑ ε : NegativeCube r, T ε δ * A ε.1

def BooleanCharacterSharpEvenInteractionStability (r : ℕ) : Prop :=
  2 ≤ r →
    (∀ (A B : BooleanCube r → ℝ) (η : ℝ),
      EvenInteractionFree B →
      0 ≤ η →
      (∀ ε : BooleanCube r, |A ε - B ε| ≤ η) →
      ∀ (T : NegativeCube r → PositiveCube r → ℝ),
        RowStochastic T →
        (∀ δ : PositiveCube r, 0 ≤ CapacitySlack A T δ) →
          (0 ≤ ∑ δ : PositiveCube r, CapacitySlack A T δ) ∧
          (∑ δ : PositiveCube r, CapacitySlack A T δ =
            ∑ ε : BooleanCube r, BooleanCharacter r ε * A ε) ∧
          (∑ δ : PositiveCube r, CapacitySlack A T δ ≤ (2 : ℝ) ^ r * η) ∧
          ((∃ δ : PositiveCube r, 0 < CapacitySlack A T δ) →
            0 < ∑ δ : PositiveCube r, CapacitySlack A T δ)) ∧
    (∀ (η C : ℝ),
      0 < η →
      η < C →
      let B : BooleanCube r → ℝ := fun _ => C
      let A : BooleanCube r → ℝ :=
        fun ε => C + η * BooleanCharacter r ε
      let T : NegativeCube r → PositiveCube r → ℝ :=
        fun _ _ => 1 / (Fintype.card (PositiveCube r) : ℝ)
      EvenInteractionFree B ∧
        (∀ ε : BooleanCube r, 0 < B ε) ∧
        (∀ ε : BooleanCube r, 0 < A ε) ∧
        (∀ ε : BooleanCube r, |A ε - B ε| ≤ η) ∧
        RowStochastic T ∧
        (∀ ε : NegativeCube r, ∀ δ : PositiveCube r, 0 ≤ T ε δ) ∧
        (∀ ε : NegativeCube r, ∀ δ : PositiveCube r, 0 < T ε δ) ∧
        (∀ δ : PositiveCube r, 0 ≤ CapacitySlack A T δ) ∧
        (∑ δ : PositiveCube r, CapacitySlack A T δ = (2 : ℝ) ^ r * η))

end MathlibPlus.Open
