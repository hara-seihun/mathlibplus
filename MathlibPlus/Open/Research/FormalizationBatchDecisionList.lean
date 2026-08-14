import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research

/-- Boolean output sequences for a list with `n` queried positions. -/
def IsBooleanOutputSequence (n : ℕ) (a : Fin (n + 1) → ℤ) : Prop :=
  ∀ i, a i = -1 ∨ a i = 1

/-- The exact suffix-contrast recurrence, with the final contrast equal to zero. -/
def IsSuffixContrast (n : ℕ) (a : Fin (n + 1) → ℤ)
    (u : Fin (n + 1) → ℚ) : Prop :=
  u ⟨n, Nat.lt_succ_self n⟩ = 0 ∧
    ∀ i : Fin n,
      u ⟨i.1, by omega⟩ =
        (a ⟨i.1 + 1, by omega⟩ : ℚ) -
          (a ⟨i.1, by omega⟩ : ℚ) +
          (1 / 2 : ℚ) * u ⟨i.1 + 1, by omega⟩

/-- The setup in Claim 51909. -/
def claim51909 (n : ℕ) (a : Fin (n + 1) → ℤ)
    (u : Fin (n + 1) → ℚ) : Prop :=
  IsBooleanOutputSequence n a ∧ IsSuffixContrast n a u

/-- Integer powers with the negative exponent used in the packet. -/
def negativePower (b : ℚ) (k : ℕ) : ℚ := b ^ (-(k : ℤ))

def alphaEnergy (n : ℕ) (u : Fin (n + 1) → ℚ) (i : Fin n) : ℚ :=
  (negativePower 2 (i.1 + 1) - negativePower 4 (i.1 + 1)) *
    (u ⟨i.1, by omega⟩) ^ 2

def tailEnergy (n : ℕ) (u : Fin (n + 1) → ℚ) (m : Fin n) : ℚ :=
  negativePower 2 (m.1 + 2) * (u ⟨m.1, by omega⟩) ^ 2

def deletionSaving (n : ℕ) (u : Fin (n + 1) → ℚ) (i : Fin n) : ℚ :=
  alphaEnergy n u i +
    Finset.sum (Finset.univ.filter (fun m : Fin n => i.1 < m.1))
      (fun m => tailEnergy n u m)

def fourierShapleyEnergy (n : ℕ) (u : Fin (n + 1) → ℚ) (i : Fin n) : ℚ :=
  alphaEnergy n u i / (i.1 + 1 : ℚ) +
    Finset.sum (Finset.univ.filter (fun m : Fin n => i.1 < m.1))
      (fun m =>
        let k := m.1 + 1
        ((k : ℚ) - 2 + negativePower 2 (k - 1)) /
            ((k : ℚ) * (k - 1)) * tailEnergy n u m)

/-- The atomwise frame, with exactly the positive-saving atoms retained. -/
def atomwiseFrame (n : ℕ) (u : Fin (n + 1) → ℚ) : ℚ :=
  Finset.sum (Finset.univ.filter (fun i : Fin n => 0 < deletionSaving n u i))
    (fun i => fourierShapleyEnergy n u i / deletionSaving n u i)

/-- The nine-output witness from Claim 51913. -/
def eightPositionWitness : Fin 9 → ℤ :=
  ![-1, 1, 1, -1, 1, -1, 1, -1, 1]

/-- Claim 51911: the frame bound through seven list positions. -/
def claim51911 : Prop :=
  ∀ n : ℕ, 1 ≤ n → n ≤ 7 →
    ∀ (a : Fin (n + 1) → ℤ) (u : Fin (n + 1) → ℚ),
      claim51909 n a u → atomwiseFrame n u ≤ 2

/-- Claim 51913: the exact eight-position witness value. -/
def claim51913 : Prop :=
  ∀ u : Fin 9 → ℚ,
    claim51909 8 eightPositionWitness u →
      atomwiseFrame 8 u =
          1099830583850023 / 524615049379575 ∧
        atomwiseFrame 8 u =
          2 + 50600485090873 / 524615049379575 ∧
        2 < atomwiseFrame 8 u

/-- Claim 51914: the witness is maximal among all eight-position Boolean lists. -/
def claim51914 : Prop :=
  ∀ (a : Fin 9 → ℤ) (u v : Fin 9 → ℚ),
    claim51909 8 a u → claim51909 8 eightPositionWitness v →
      atomwiseFrame 8 u ≤ atomwiseFrame 8 v

end MathlibPlus.Open.Research
