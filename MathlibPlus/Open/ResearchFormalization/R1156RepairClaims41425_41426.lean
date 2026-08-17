import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1156RepairClaims41425_41426

noncomputable section

abbrev F7 := ZMod 7

def translate (B : Finset F7) (t : F7) : Finset F7 :=
  B.image (fun b => b + t)

def permute (π : Equiv.Perm F7) (B : Finset F7) : Finset F7 :=
  B.image π

def normalizedDevelopmentLabel
    (B : Finset F7) (π : Equiv.Perm F7) (δ : F7 → F7) : Prop :=
  Function.Bijective δ ∧ δ 0 = 0 ∧
    ∀ t : F7,
      permute π (translate B t) = translate (permute π B) (δ t)

def scalarLabel (δ : F7 → F7) : Prop :=
  ∃ c : F7, c ≠ 0 ∧ ∀ t : F7, δ t = c * t

def nonlinearNormalizedLabel (δ : F7 → F7) : Prop :=
  ∃ (B : Finset F7) (π : Equiv.Perm F7),
    2 ≤ B.card ∧ B.card ≤ 5 ∧
      normalizedDevelopmentLabel B π δ ∧ ¬ scalarLabel δ

def relativeDerivative (δ : F7 → F7) (r : F7) : F7 → F7 :=
  fun s => δ (r + s) - δ r

def shiftedCompatibilityEquation
    (X : Finset F7) (r : (↥X) → F7)
    (labels : F7 → F7 → F7) : Prop :=
  ∀ (x x' : X) (y : F7),
    relativeDerivative (labels y) (r x) =
      relativeDerivative
        (labels (y + (x' : F7) - (x : F7))) (r x')

abbrev SupportOfSize (k : ℕ) :=
  {X : Finset F7 // X.card = k}

noncomputable def supportAnchor {k : ℕ} (hk : 2 ≤ k)
    (X : SupportOfSize k) : X.1 :=
  have hcard : 0 < X.1.card := by omega
  Classical.choice
    ((Finset.nonempty_coe_sort).2
      ((Finset.card_pos (s := X.1)).mp hcard))

abbrev OffsetData (k : ℕ) :=
  Σ X : SupportOfSize k, (↥X.1 → F7)

abbrev NormalizedOffsetAssignments (k : ℕ) (hk : 2 ≤ k) :=
  {z : OffsetData k // z.2 (supportAnchor hk z.1) = 0}

def assignmentSupport {k : ℕ} {hk : 2 ≤ k}
    (z : NormalizedOffsetAssignments k hk) : Finset F7 :=
  z.1.1.1

def assignmentOffsets {k : ℕ} {hk : 2 ≤ k}
    (z : NormalizedOffsetAssignments k hk) :
    (↥(assignmentSupport z)) → F7 :=
  z.1.2

def assignmentAnchor {k : ℕ} {hk : 2 ≤ k}
    (z : NormalizedOffsetAssignments k hk) :
    (↥(assignmentSupport z)) :=
  supportAnchor hk z.1.1

def assignmentIsAffine {k : ℕ} {hk : 2 ≤ k}
    (z : NormalizedOffsetAssignments k hk) : Prop :=
  ∃ m : F7, ∀ x : assignmentSupport z,
    assignmentOffsets z x = m * ((x : F7) - (assignmentAnchor z : F7))

def assignmentIsSolvable {k : ℕ} {hk : 2 ≤ k}
    (z : NormalizedOffsetAssignments k hk) : Prop :=
  ∃ labels : F7 → F7 → F7,
    (∀ y : F7, nonlinearNormalizedLabel (labels y)) ∧
      shiftedCompatibilityEquation
        (assignmentSupport z) (assignmentOffsets z) labels

abbrev SolvableOffsetAssignments (k : ℕ) (hk : 2 ≤ k) :=
  {z : NormalizedOffsetAssignments k hk // assignmentIsSolvable z}

abbrev CompatibleStateFamilies (k : ℕ) (hk : 2 ≤ k) :=
  {z : Σ _z₀ : NormalizedOffsetAssignments k hk, (F7 → F7 → F7) //
    (∀ y : F7, nonlinearNormalizedLabel (z.2 y)) ∧
      shiftedCompatibilityEquation
        (assignmentSupport z.1) (assignmentOffsets z.1) z.2}

abbrev NonaffineSolvableOffsetAssignments (k : ℕ) (hk : 2 ≤ k) :=
  {z : NormalizedOffsetAssignments k hk //
    assignmentIsSolvable z ∧ ¬ assignmentIsAffine z}

def tableRow (k : ℕ) (hk : 2 ≤ k) (all solvable states nonaffine : ℕ) : Prop :=
  Nat.card (NormalizedOffsetAssignments k hk) = all ∧
    Nat.card (SolvableOffsetAssignments k hk) = solvable ∧
    Nat.card (CompatibleStateFamilies k hk) = states ∧
    Nat.card (NonaffineSolvableOffsetAssignments k hk) = nonaffine

/-- Claim 41425: the six exact support-size rows, with each count attached to
    the normalized offset, solvability, compatible-family, and nonaffine
    solvability carriers. -/
def explicitCompleteCountTable_claim41425 : Prop :=
  tableRow 2 (by omega) 147 147 12348 0 ∧
    tableRow 3 (by omega) 1715 245 20580 0 ∧
    tableRow 4 (by omega) 12005 245 20580 0 ∧
    tableRow 5 (by omega) 50421 147 12348 0 ∧
    tableRow 6 (by omega) 117649 49 4116 0 ∧
    tableRow 7 (by omega) 117649 7 588 0

/-- Claim 41426: the complete normalized assignment carrier has 299586
    elements, and its nonaffine solvable subcarrier is empty in every row. -/
def noNonaffineCompatibleAssignment_claim41426 : Prop :=
  (Nat.card (NormalizedOffsetAssignments 2 (by omega)) +
      Nat.card (NormalizedOffsetAssignments 3 (by omega)) +
      Nat.card (NormalizedOffsetAssignments 4 (by omega)) +
      Nat.card (NormalizedOffsetAssignments 5 (by omega)) +
      Nat.card (NormalizedOffsetAssignments 6 (by omega)) +
      Nat.card (NormalizedOffsetAssignments 7 (by omega)) = 299586) ∧
    Nat.card (NonaffineSolvableOffsetAssignments 2 (by omega)) = 0 ∧
    Nat.card (NonaffineSolvableOffsetAssignments 3 (by omega)) = 0 ∧
    Nat.card (NonaffineSolvableOffsetAssignments 4 (by omega)) = 0 ∧
    Nat.card (NonaffineSolvableOffsetAssignments 5 (by omega)) = 0 ∧
    Nat.card (NonaffineSolvableOffsetAssignments 6 (by omega)) = 0 ∧
    Nat.card (NonaffineSolvableOffsetAssignments 7 (by omega)) = 0

end

end MathlibPlus.Open.ResearchFormalization.R1156RepairClaims41425_41426
