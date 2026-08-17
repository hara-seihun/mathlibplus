import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1967

noncomputable section

abbrev Cube (n : ℕ) := Fin n → Bool
abbrev BinaryVector (n : ℕ) := Fin n → ZMod 2
abbrev OmittedVector (n : ℕ) (i : Fin n) := {j : Fin n // j ≠ i} → ZMod 2
abbrev DirectionFunction (n : ℕ) (i : Fin n) := OmittedVector n i → Bool
abbrev QuotientVector (r : ℕ) := Fin r → ZMod 2

def flipAt {n : ℕ} (i : Fin n) (x : Cube n) : Cube n :=
  Function.update x i (!x i)

def basepointVector {n : ℕ} (i : Fin n) (x : Cube n) : OmittedVector n i :=
  fun j => if x j.1 then 1 else 0

def cubeSelectedEdge {n : ℕ}
    (f : ∀ i : Fin n, DirectionFunction n i)
    (i : Fin n) (x : Cube n) : Prop :=
  x i = false ∧ f i (basepointVector i x) = true

def coordinateSquareHasUnselected {n : ℕ}
    (f : ∀ i : Fin n, DirectionFunction n i) : Prop :=
  ∀ i j : Fin n, i ≠ j → ∀ x : Cube n,
    x i = false → x j = false →
      ¬ (cubeSelectedEdge f i x ∧ cubeSelectedEdge f j x ∧
        cubeSelectedEdge f i (flipAt j x) ∧
        cubeSelectedEdge f j (flipAt i x))

def quotientTranslationStabilizer {n : ℕ} {i : Fin n}
    (f : OmittedVector n i → Bool) : Set (OmittedVector n i) :=
  {v | ∀ x, f (x + v) = f x}

def affineHyperplane {r : ℕ}
    (ell : QuotientVector r →+ ZMod 2) (c : ZMod 2) :
    Set (QuotientVector r) :=
  {x | ell x = c}

def losslessHyperplanePlusPoint {n r : ℕ} {i : Fin n}
    (f : DirectionFunction n i) : Prop :=
  ∃ F : OmittedVector n i →+ QuotientVector r,
    ∃ ell : QuotientVector r →+ ZMod 2,
    ∃ c : ZMod 2,
    ∃ m : QuotientVector r,
      Function.Surjective F ∧
      ell ≠ 0 ∧
      ell m ≠ c ∧
      (∀ x, f x = true ↔ (ell (F x) = c ∨ F x = m)) ∧
      (∀ v, v ∈ quotientTranslationStabilizer f ↔ F v = 0)

def hyperplanePlusOneDirections {n r : ℕ}
    (f : ∀ i : Fin n, DirectionFunction n i) : Set (Fin n) :=
  {i | losslessHyperplanePlusPoint (r := r) (f i)}

/-- Claim 36600: the exact tier of directions with literal quotient
`𝔽₂^r` and a hyperplane-plus-one selected quotient set obeys the all-rank
bound in every C4-free hypercube subgraph. -/
def claim36600_allRankHyperplanePlusOneBound : Prop :=
  ∀ n r : ℕ, 2 ≤ r →
    ∀ f : ∀ i : Fin n, DirectionFunction n i,
      coordinateSquareHasUnselected f →
        let q : ℕ := 2 ^ r
        (Set.ncard (hyperplanePlusOneDirections (r := r) f) : ℚ) ≤
          ((q : ℚ) ^ 3 - 2 * (q : ℚ) ^ 2 + 2 * (q : ℚ)) / 2

end
end MathlibPlus.Open.ResearchFormalization.R1967
