import Mathlib

namespace MathlibPlus.Open.ProjectsResearch

noncomputable section

abbrev AlignmentIndex (r : ℕ) := Fin (r + 1) × Fin (r + 1)

noncomputable def character (r : ℕ) (z : ℂˣ) : ℂ :=
  Finset.sum (Finset.range (r + 1)) (fun j =>
    ((z ^ (Int.ofNat r - Int.ofNat (2 * j)) : ℂˣ) : ℂ))

def alignmentPlusTrace (r : ℕ) (y α : ℂˣ) : ℂ :=
  character r (y * α)

def alignmentMinusTrace (r : ℕ) (y α : ℂˣ) : ℂ :=
  character r (y / α)

def alignmentDifference (r : ℕ) (y α : ℂˣ) : ℂ :=
  alignmentPlusTrace r y α - alignmentMinusTrace r y α

def fullCharacter (r : ℕ) (y α : ℂˣ) : ℂ :=
  character r y * character r α

def sphericalBasic (y α : ℂˣ) (X : ℂ) : ℂ :=
  1 / ((1 - X) *
    (1 - (y : ℂ) * (α : ℂ) * X) *
    (1 - (y : ℂ) * (α⁻¹ : ℂˣ) * X) *
    (1 - (y⁻¹ : ℂˣ) * (α : ℂ) * X) *
    (1 - (y⁻¹ : ℂˣ) * (α⁻¹ : ℂˣ) * X))

def diagonalAlignmentProjector (r : ℕ) :
    Matrix (AlignmentIndex r) (AlignmentIndex r) ℂ :=
  fun a b => if a = b ∧ a.1 = a.2 then 1 else 0

def antiDiagonalAlignmentProjector (r : ℕ) :
    Matrix (AlignmentIndex r) (AlignmentIndex r) ℂ :=
  fun a b => if a = b ∧ a.1.1 + a.2.1 = r then 1 else 0

def reverseWeight (r : ℕ) (i : Fin (r + 1)) : Fin (r + 1) :=
  ⟨r - i.1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩

def reverseSecondFactor (r : ℕ) (a : AlignmentIndex r) : AlignmentIndex r :=
  (a.1, reverseWeight r a.2)

def secondWeylConjugate (r : ℕ)
    (M : Matrix (AlignmentIndex r) (AlignmentIndex r) ℂ) :
    Matrix (AlignmentIndex r) (AlignmentIndex r) ℂ :=
  fun a b => M (reverseSecondFactor r a) (reverseSecondFactor r b)

def scalarObservation (r : ℕ) (y α : ℂˣ) (X : ℂ) : ℂ × ℂ :=
  (fullCharacter r y α, sphericalBasic y α X)

/--
Reversal of the second torus parameter exchanges the two alignment supports.
Their signed difference is therefore Weyl-odd, whereas the full character and
spherical basic function are Weyl-even.  Consequently no scalar evaluation
factoring through those Weyl-even values can recover that difference or the
ordered signed channel row.
-/
def sphericalTraceCannotSelectSignedAlignmentCurrent : Prop :=
  (∀ r : ℕ, secondWeylConjugate r (diagonalAlignmentProjector r) =
      antiDiagonalAlignmentProjector r) ∧
  (∀ r : ℕ, secondWeylConjugate r (antiDiagonalAlignmentProjector r) =
      diagonalAlignmentProjector r) ∧
  (∀ r : ℕ, ∀ y α : ℂˣ,
    alignmentPlusTrace r y (α⁻¹) = alignmentMinusTrace r y α ∧
    alignmentMinusTrace r y (α⁻¹) = alignmentPlusTrace r y α) ∧
  (∀ r : ℕ, ∀ y α : ℂˣ,
    alignmentDifference r y (α⁻¹) = -alignmentDifference r y α) ∧
  (∀ r : ℕ, ∀ y α : ℂˣ,
    fullCharacter r y (α⁻¹) = fullCharacter r y α) ∧
  (∀ y α : ℂˣ, ∀ X : ℂ,
    sphericalBasic y (α⁻¹) X = sphericalBasic y α X) ∧
  (∃ r : ℕ, ∃ y α : ℂˣ, alignmentDifference r y α ≠ 0) ∧
  (¬ ∃ recover : ℕ → ℂ → (ℂ × ℂ) → ℂ,
    ∀ r : ℕ, ∀ X : ℂ, ∀ y α : ℂˣ,
      recover r X (scalarObservation r y α X) =
        alignmentDifference r y α) ∧
  (¬ ∃ determine : ℕ → ℂ → (ℂ × ℂ) → (ℂ × ℂ),
    ∀ r : ℕ, ∀ X : ℂ, ∀ y α : ℂˣ,
      determine r X (scalarObservation r y α X) =
        (alignmentPlusTrace r y α, alignmentMinusTrace r y α))

end

end MathlibPlus.Open.ProjectsResearch
