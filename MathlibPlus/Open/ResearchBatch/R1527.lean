import Mathlib

noncomputable section
open MeasureTheory
open scoped BigOperators Interval

namespace MathlibPlus.Open.ResearchBatch.R1527

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev RowSpace (F : Type*) (m : ℕ) := Fin m → F
abbrev Ambient (F : Type*) (m : ℕ) := RowSpace F m × F

def rowPlane (n : RowSpace F m →ₗ[F] F) (a ell : F) : Set (Ambient F m) :=
  {x | n x.1 = ell ∧ x.2 = a}

def rowPlaneUnion (A : Finset F) (n : F → RowSpace F m →ₗ[F] F)
    (L : F → Finset F) : Set (Ambient F m) :=
  {x | ∃ a ∈ A, ∃ ell ∈ L a, n a x.1 = ell ∧ x.2 = a}

def translateLabels (L : Finset F) (t : F) : Finset F := L.image (fun ell => ell + t)

def differenceMultiplicity (S : Set (Ambient F m)) (v : RowSpace F m) (c : F) : ℕ :=
  (by classical
    exact (Finset.univ.filter (fun xy : Ambient F m × Ambient F m =>
      xy.1 ∈ S ∧ xy.2 ∈ S ∧ xy.1 - xy.2 = (v, c))).card)

def rowPlaneUnion_claim38129 (m : ℕ) (A : Finset F)
    (n : F → RowSpace F m →ₗ[F] F) (L : F → Finset F) : Set (Ambient F m) :=
  {x | ∃ a ∈ A, ∃ ell ∈ L a, n a x.1 = ell ∧ x.2 = a}

def sameRowSolutionCount_claim38132 : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (n : RowSpace F m →ₗ[F] F), n ≠ 0 →
    ∀ ell k : F, ∀ v : RowSpace F m,
      Fintype.card {w : RowSpace F m // n (w + v) = ell ∧ n w = k} =
        if n v = ell - k then Fintype.card F ^ (m - 1) else 0

def projectivelyDistinct (A : Finset F)
    (n : F → RowSpace F m →ₗ[F] F) : Prop :=
  (∀ a ∈ A, n a ≠ 0) ∧
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b →
    ∀ scale : F, n a ≠ scale • n b

def crossRowCount (A : Finset F) (L : F → Finset F) (c : F) : ℕ :=
  ∑ a ∈ A, ∑ b ∈ A,
    if a ≠ b ∧ a - b = c then (L a).card * (L b).card else 0

-- The label family is an explicit argument of the exact formula below.
def exactDifferenceFormula_claim38133 : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (A : Finset F)
    (n : F → RowSpace F m →ₗ[F] F) (L : F → Finset F),
    projectivelyDistinct A n → ∀ v : RowSpace F m, ∀ c : F,
    differenceMultiplicity (rowPlaneUnion A n L) v c =
      Fintype.card F ^ (m - 2) * crossRowCount A L c +
        (if c = 0 then Fintype.card F ^ (m - 1) *
          (∑ a ∈ A,
            Fintype.card {ellk : F × F //
              ellk.1 ∈ L a ∧ ellk.2 ∈ L a ∧ ellk.1 - ellk.2 = n a v})
         else 0)

def independentRowShifts_claim38134 : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (A : Finset F)
    (n : F → RowSpace F m →ₗ[F] F) (L : F → Finset F),
    projectivelyDistinct A n → ∀ (t : F → F), ∀ v : RowSpace F m, ∀ c : F,
    differenceMultiplicity (rowPlaneUnion A n L) v c =
      differenceMultiplicity
        (rowPlaneUnion A n (fun a => translateLabels (L a) (t a))) v c

end MathlibPlus.Open.ResearchBatch.R1527
