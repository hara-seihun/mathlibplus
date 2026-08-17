import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1156

noncomputable section

abbrev F7 := ZMod 7

/-- The translate of a finite subset of `F₇` by an element of `F₇`. -/
def translate (B : Finset F7) (t : F7) : Finset F7 :=
  B.image (fun b => b + t)

/-- The image of a finite subset under a permutation of `F₇`. -/
def permute (π : Equiv.Perm F7) (B : Finset F7) : Finset F7 :=
  B.image π

/-- A normalized label map induced by a translation-development
    isomorphism, with its exact source equation. -/
def normalizedDevelopmentLabel
    (B : Finset F7) (π : Equiv.Perm F7) (δ : F7 → F7) : Prop :=
  Function.Bijective δ ∧
    δ 0 = 0 ∧
      ∀ t : F7,
        permute π (translate B t) =
          translate (permute π B) (δ t)

/-- The six scalar normalized label maps are the nonzero scalar maps. -/
def scalarLabel (δ : F7 → F7) : Prop :=
  ∃ c : F7, c ≠ 0 ∧ ∀ t : F7, δ t = c * t

/-- The nonlinear normalized labels from the exact `C₇` translation-
    development carrier: subset sizes two through five, normalized at zero,
    and not one of the scalar labels. -/
def nonlinearNormalizedLabel (δ : F7 → F7) : Prop :=
  ∃ (B : Finset F7) (π : Equiv.Perm F7),
    2 ≤ B.card ∧ B.card ≤ 5 ∧
      normalizedDevelopmentLabel B π δ ∧ ¬ scalarLabel δ

/-- The relative derivative used in the compatibility equation. -/
def relativeDerivative (δ : F7 → F7) (r : F7) : F7 → F7 :=
  fun s => δ (r + s) - δ r

/-- The displayed shifted compatibility equation for a support and an
    offset assignment. -/
def shiftedCompatibilityEquation
    (X : Finset F7) (r : (↥X) → F7)
    (labels : F7 → F7 → F7) : Prop :=
  ∀ (x x' : X) (y : F7),
    relativeDerivative (labels y) (r x) =
      relativeDerivative
        (labels (y + (x' : F7) - (x : F7))) (r x')

/-- Claim 31657: after choosing an anchor and normalizing its offset, the
    label-family compatibility relation is exactly the displayed equality of
    relative-derivative functions. -/
def shiftedDerivativeCompatibility_claim31657
    (X : Finset F7) (_hX : 2 ≤ X.card) (a : X)
    (r : (↥X) → F7) (_hr : r a = 0)
    (labels : F7 → F7 → F7) : Prop :=
  shiftedCompatibilityEquation X r labels

/-- Claim 31658: a normalized offset assignment has a compatible family of
    nonlinear labels exactly when the offsets are affine from the anchor. -/
def compatibilityForcesAffineSupportOffsets_claim31658 : Prop :=
  ∀ (X : Finset F7) (a : X) (r : (↥X) → F7),
    2 ≤ X.card →
      r a = 0 →
        ((∃ labels : F7 → F7 → F7,
            (∀ y : F7, nonlinearNormalizedLabel (labels y)) ∧
              shiftedCompatibilityEquation X r labels) ↔
          (∃ m : F7,
            ∀ x : X,
              r x = m * ((x : F7) - (a : F7))))

/-- Claim 31659: every affine normalized assignment has exactly 84
    compatible nonlinear label families. -/
def exactlyEightyFourCompatibleFamilies_claim31659 : Prop :=
  ∀ (X : Finset F7) (a : X) (r : (↥X) → F7),
    2 ≤ X.card →
      r a = 0 →
        (∃ m : F7,
          ∀ x : X,
            r x = m * ((x : F7) - (a : F7))) →
          Nat.card
              {labels : F7 → F7 → F7 //
                (∀ y : F7, nonlinearNormalizedLabel (labels y)) ∧
                  shiftedCompatibilityEquation X r labels} = 84

abbrev SupportOfSize (k : ℕ) :=
  {X : Finset F7 // X.card = k}

/-- A fixed anchor chosen from a support of size at least two.  The source
    permits an anchor in the support; this choice makes the support-size
    carriers canonical without adding any offset data. -/
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
    assignmentOffsets z x =
      m * ((x : F7) - (assignmentAnchor z : F7))

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

/-- Claim 31660: the complete support-size count, including normalized
    assignments, solvable assignments, affine support offsets, and compatible
    state families. -/
def completeSupportSizeCountingFormula_claim31660 : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k), k ≤ 7 →
    Nat.card (NormalizedOffsetAssignments k hk) =
        Nat.choose 7 k * 7 ^ (k - 1) ∧
      Nat.card (SolvableOffsetAssignments k hk) =
        7 * Nat.choose 7 k ∧
      (∀ z : NormalizedOffsetAssignments k hk,
        assignmentIsSolvable z → assignmentIsAffine z) ∧
      Nat.card (CompatibleStateFamilies k hk) =
        84 * 7 * Nat.choose 7 k

end

end MathlibPlus.Open.ResearchFormalization.R1156
