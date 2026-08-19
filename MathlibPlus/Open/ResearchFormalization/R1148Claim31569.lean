import MathlibPlus.Open.ResearchFormalization.R1148Claim41326

namespace MathlibPlus.Open.ResearchFormalization.R1148Claim31569

open MathlibPlus.Open.ResearchFormalization.R1148Claim41326

noncomputable section

abbrev DevelopmentLabel := Equiv.Perm C7

/-- The least-residue anchor of a finite support. -/
def leastAnchor (X : Set C7) (a : X) : Prop :=
  ∀ x : X, ZMod.val (a : C7) ≤ ZMod.val (x : C7)

/-- Supports in the six sizes covered by the classification. -/
def supportCondition (X : Set C7) : Prop :=
  2 ≤ X.ncard ∧ X.ncard ≤ 7

abbrev Support := {X : Set C7 // supportCondition X}
abbrev OffsetData := Σ X : Support, (X.1 → C7)

def normalizedOffsetData (z : OffsetData) : Prop :=
  ∃ a : z.1.1, leastAnchor z.1.1 a ∧ z.2 a = 0

abbrev NormalizedOffsetAssignments :=
  {z : OffsetData // normalizedOffsetData z}

def assignmentSupport (z : NormalizedOffsetAssignments) : Set C7 :=
  z.1.1.1

def assignmentOffsets (z : NormalizedOffsetAssignments) :
    assignmentSupport z → C7 :=
  z.1.2

/-- The relative derivative displayed in the compatibility equation. -/
def relativeDerivative (r : C7) (δ : DevelopmentLabel) : C7 → C7 :=
  fun s => δ (r + s) - δ r

/-- A state family is indexed by `C₇`, takes values in the exact nonlinear
label carrier, and satisfies every displayed shifted-derivative equation. -/
def compatibleFamily (X : Set C7) (r : X → C7)
    (δ : C7 → DevelopmentLabel) : Prop :=
  (∀ y : C7,
      δ y ∈
        MathlibPlus.Open.ResearchFormalization.R1148Claim41326.nonlinearLabels) ∧
    ∀ (x x' : X) (y : C7),
      relativeDerivative (r x) (δ y) =
        relativeDerivative (r x')
          (δ (y + (x' : C7) - (x : C7)))

def assignmentIsAffine (z : NormalizedOffsetAssignments) : Prop :=
  ∃ (a : assignmentSupport z),
    leastAnchor (assignmentSupport z) a ∧
      assignmentOffsets z a = 0 ∧
        ∃ m : C7, ∀ x : assignmentSupport z,
          assignmentOffsets z x =
            m * ((x : C7) - (a : C7))

def assignmentIsSolvable (z : NormalizedOffsetAssignments) : Prop :=
  ∃ δ : C7 → DevelopmentLabel,
    compatibleFamily (assignmentSupport z) (assignmentOffsets z) δ

abbrev CompatibleStateFamilies :=
  {z : Σ q : NormalizedOffsetAssignments, (C7 → DevelopmentLabel) //
    compatibleFamily (assignmentSupport z.1) (assignmentOffsets z.1) z.2}

abbrev NonaffineSolvableOffsetAssignments :=
  {z : NormalizedOffsetAssignments //
    assignmentIsSolvable z ∧ ¬ assignmentIsAffine z}

/-- The complete shifted-derivative compatibility classification. -/
def claim31569 : Prop :=
  Set.ncard nonlinearLabels = 84 ∧
    (∀ (X : Set C7) (a : X) (r : X → C7),
      supportCondition X →
        leastAnchor X a →
          r a = 0 →
            ((∃ δ : C7 → DevelopmentLabel,
                compatibleFamily X r δ) ↔
              ∃ m : C7, ∀ x : X,
                r x = m * ((x : C7) - (a : C7))) ∧
              ((∃ m : C7, ∀ x : X,
                  r x = m * ((x : C7) - (a : C7))) →
                Nat.card
                  {δ : C7 → DevelopmentLabel //
                    compatibleFamily X r δ} = 84)) ∧
      Nat.card NormalizedOffsetAssignments = 299586 ∧
        Nat.card NonaffineSolvableOffsetAssignments = 0

end

end MathlibPlus.Open.ResearchFormalization.R1148Claim31569
