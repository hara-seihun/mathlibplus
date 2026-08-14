import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationBatch

noncomputable section

section SemidirectProduct

variable {p : ℕ} {H : Type*} [Group H] [Fintype H] [DecidableEq H]

def sdMul (χ : H →* (ZMod p)ˣ) (x y : ZMod p × H) : ZMod p × H :=
  (x.1 + (χ x.2 : ZMod p) * y.1, x.2 * y.2)

def sdInv (χ : H →* (ZMod p)ˣ) (x : ZMod p × H) : ZMod p × H :=
  (-((χ (x.2⁻¹) : (ZMod p)ˣ) : ZMod p) * x.1, x.2⁻¹)

def sdOne : ZMod p × H := (0, 1)

def fibreMap (φ : H → Equiv.Perm (ZMod p)) (x : ZMod p × H) : ZMod p × H :=
  (φ x.2 x.1, x.2)

def zeroFixingProfile (φ : H → Equiv.Perm (ZMod p)) : Prop :=
  (∀ h, φ h 0 = 0) ∧ φ 1 = Equiv.refl (ZMod p)

def sdCayleyEdge (χ : H →* (ZMod p)ˣ)
    (S : Finset (ZMod p × H)) (x y : ZMod p × H) : Prop :=
  ∃ s, s ∈ S ∧ y = sdMul χ x s

def normalizedCayleyPresentationIso (χ : H →* (ZMod p)ˣ)
    (S : Finset (ZMod p × H)) (φ : H → Equiv.Perm (ZMod p)) : Prop :=
  Function.Bijective (fibreMap φ) ∧
    fibreMap φ sdOne = sdOne ∧
      ∀ x y,
        sdCayleyEdge χ S x y ↔
          sdCayleyEdge χ S (fibreMap φ x) (fibreMap φ y)

def claim44215 : Prop :=
  ∀ (hp : Nat.Prime p) (hop : Odd p)
    (χ : H →* (ZMod p)ˣ),
    (∀ h, (χ h : ZMod p) = 1 ∨ (χ h : ZMod p) = -1) →
    ∀ (φ : H → Equiv.Perm (ZMod p)),
      zeroFixingProfile φ →
      ∀ S : Finset (ZMod p × H),
        normalizedCayleyPresentationIso χ S φ →
          Finset.image (fibreMap φ) S = S

def claim44216 : Prop :=
  ∀ (hp : Nat.Prime p) (hop : Odd p)
    (χ : H →* (ZMod p)ˣ),
    (∀ h, (χ h : ZMod p) = 1 ∨ (χ h : ZMod p) = -1) →
    ∀ (φ : H → Equiv.Perm (ZMod p)),
      zeroFixingProfile φ →
      let F := fibreMap φ
      (∀ (a : ZMod p) (h : H),
          let s : ZMod p × H := (a, h)
          let g : ZMod p × H := (0, h⁻¹)
          sdMul χ s g = (a, 1) ∧
            F (sdMul χ s g) = sdMul χ s g ∧
            F g = g ∧
            sdMul χ (F (sdMul χ s g)) (sdInv χ (F g)) = s) ∧
        ∀ S : Finset (ZMod p × H),
          normalizedCayleyPresentationIso χ S φ →
            (∀ s, F s ∈ S → s ∈ S) ∧ Finset.image F S = S

end SemidirectProduct

section CollapsedC9

abbrev BinaryBase (r : ℕ) := Fin r → ZMod 2
abbrev CollapsedGroup (r : ℕ) := BinaryBase r × ZMod 9

inductive CollapsedSection
  | empty
  | zero
  | nonzero
  | all
  deriving DecidableEq

def collapsedSectionSet : CollapsedSection → Finset (ZMod 9)
  | .empty => ∅
  | .zero => {0}
  | .nonzero => (Finset.univ : Finset (ZMod 9)).erase 0
  | .all => Finset.univ

def c9Section (S : Finset (CollapsedGroup r)) (v : BinaryBase r) : Finset (ZMod 9) :=
  (S.filter (fun x => x.1 = v)).image (fun x => x.2)

def isCollapsedSection (T : Finset (ZMod 9)) : Prop :=
  T = ∅ ∨
    T = ({0} : Finset (ZMod 9)) ∨
      T = (Finset.univ : Finset (ZMod 9)).erase 0 ∨
        T = Finset.univ

def sectionEpsilon (T : Finset (ZMod 9)) : ℂ :=
  if T = ∅ then 0
  else if T = ({0} : Finset (ZMod 9)) then 1
  else if T = (Finset.univ : Finset (ZMod 9)).erase 0 then -1
  else 0

def inverseClosed (S : Finset (CollapsedGroup r)) : Prop :=
  ∀ x, x ∈ S ↔ -x ∈ S

def c9P (v : BinaryBase r) (u : BinaryBase r → ℂ) (x : BinaryBase r) : ℂ :=
  u (x + v)

def c9TrivialBlock (S : Finset (CollapsedGroup r))
    (u : BinaryBase r → ℂ) (x : BinaryBase r) : ℂ :=
  ∑ v : BinaryBase r, (c9Section S v).card * c9P v u x

def c9NontrivialBlock (S : Finset (CollapsedGroup r)) (ζ : ℂ)
    (u : BinaryBase r → ℂ) (x : BinaryBase r) : ℂ :=
  ∑ v : BinaryBase r, sectionEpsilon (c9Section S v) * c9P v u x

def c9Lift (ζ : ℂ) (u : BinaryBase r → ℂ)
    (x : CollapsedGroup r) : ℂ :=
  ζ ^ x.2.val * u x.1

def c9Adjacency (S : Finset (CollapsedGroup r))
    (f : CollapsedGroup r → ℂ) (x : CollapsedGroup r) : ℂ :=
  Finset.sum S (fun y => f (x + y))

def claim44240 : Prop :=
  ∀ (r : ℕ), r ≤ 5 →
    ∀ S : Finset (CollapsedGroup r),
      inverseClosed S →
      (∀ v, isCollapsedSection (c9Section S v)) →
      (∀ v,
          sectionEpsilon (c9Section S v) = 0 ∨
            sectionEpsilon (c9Section S v) = 1 ∨
            sectionEpsilon (c9Section S v) = -1) ∧
      (∀ (u : BinaryBase r → ℂ) (x : BinaryBase r) (a : ZMod 9),
          c9Adjacency S (c9Lift 1 u) (x, a) = c9TrivialBlock S u x) ∧
      (∀ (ζ : ℂ), ζ ^ 9 = 1 → ζ ≠ 1 →
        ∀ (u : BinaryBase r → ℂ) (x : BinaryBase r) (a : ZMod 9),
          c9Adjacency S (c9Lift ζ u) (x, a) =
            ζ ^ a.val * c9NontrivialBlock S ζ u x)

abbrev MarkedConnection (r : ℕ) := BinaryBase r × ZMod 9

def markedConnection (τ : BinaryBase r → CollapsedSection) : Finset (MarkedConnection r) :=
  Finset.univ.filter (fun x => x.2 ∈ collapsedSectionSet (τ x.1))

def markedRelation (τ : BinaryBase r → CollapsedSection)
    (x y : MarkedConnection r) : Prop :=
  (y.1 - x.1, y.2 - x.2) ∈ markedConnection τ

def fibrePermutationMap (π : BinaryBase r → Equiv.Perm (ZMod 9))
    (x : MarkedConnection r) : MarkedConnection r :=
  (x.1, π x.1 x.2)

def markedPreserving (τ : BinaryBase r → CollapsedSection)
    (π : BinaryBase r → Equiv.Perm (ZMod 9)) : Prop :=
  ∀ x y, markedRelation τ x y ↔
    markedRelation τ (fibrePermutationMap π x) (fibrePermutationMap π y)

def sensitiveMarkedRelation (τ : BinaryBase r → CollapsedSection)
    (x y : MarkedConnection r) : Prop :=
  sectionEpsilon (collapsedSectionSet (τ (y.1 - x.1))) ≠ 0 ∧
    markedRelation τ x y

def markedSensitiveOffsets (τ : BinaryBase r → CollapsedSection) : Finset (BinaryBase r) :=
  Finset.univ.filter (fun v =>
    sectionEpsilon (collapsedSectionSet (τ v)) ≠ 0)

def markedSpan (τ : BinaryBase r → CollapsedSection) : AddSubgroup (BinaryBase r) :=
  AddSubgroup.closure (markedSensitiveOffsets τ : Set (BinaryBase r))

def constantOnMarkedCosets (τ : BinaryBase r → CollapsedSection)
    (π : BinaryBase r → Equiv.Perm (ZMod 9)) : Prop :=
  ∀ x y, x - y ∈ markedSpan τ → π x = π y

def claim44241 : Prop :=
  ∀ (r : ℕ), r ≤ 5 →
    ∀ (τ : BinaryBase r → CollapsedSection),
      (∀ v, v ∉ markedSpan τ → τ v = .empty ∨ τ v = .all) ∧
      (∀ x y, sensitiveMarkedRelation τ x y → y.1 - x.1 ∈ markedSpan τ) ∧
      ∀ π : BinaryBase r → Equiv.Perm (ZMod 9),
        markedPreserving τ π ↔ constantOnMarkedCosets τ π

end CollapsedC9

section BinaryArithmetic

def claim44245 : Prop :=
  ∀ (D : Finset ℕ) (n m : ℕ) (hD : D.Nonempty),
    (∀ d ∈ D, 0 < d) →
    m ∈ D →
    D.max' hD = m →
    ((n : ℚ) = Finset.sum D (fun d => ((n + d : ℕ) : ℚ) / (2 : ℚ) ^ d)) ↔
      (2 : ℚ) ^ (m + 1) =
        (n : ℚ) + (m : ℚ) + 2 +
          Finset.sum ((Finset.Icc 1 m).filter (fun d => d ∉ D))
            (fun d => ((n + d : ℕ) : ℚ) * (2 : ℚ) ^ (m - d))

noncomputable def realBinaryValue (d : ℕ → ℝ) : ℝ :=
  tsum (fun j : ℕ => if 0 < j then d j / (2 : ℝ) ^ j else 0)

noncomputable def realBinaryMoment (d : ℕ → ℝ) : ℝ :=
  tsum (fun j : ℕ =>
    if 0 < j then (j : ℝ) * d j / (2 : ℝ) ^ j else 0)

def binaryValue (d : ℕ → ℕ) : ℝ :=
  realBinaryValue (fun j => (d j : ℝ))

def binaryMoment (d : ℕ → ℕ) : ℝ :=
  realBinaryMoment (fun j => (d j : ℝ))

def binaryDigits (d : ℕ → ℕ) : Prop :=
  ∀ j, d j = 0 ∨ d j = 1

def eventuallyBinaryDigit (d : ℕ → ℕ) (b : ℕ) : Prop :=
  ∃ p, ∀ j, p ≤ j → d j = b

def awayFromBinaryAmbiguity (d : ℕ → ℕ) : Prop :=
  ¬ eventuallyBinaryDigit d 0 ∧ ¬ eventuallyBinaryDigit d 1

def realFractionalPart (x : ℝ) : ℝ :=
  x - (Int.floor x : ℝ)

noncomputable def rhoTwo (y : ℝ) : ℝ :=
  tsum (fun i : ℕ =>
    realFractionalPart ((2 : ℝ) ^ i * y) / (2 : ℝ) ^ i)

def claim44256 : Prop :=
  ∀ (d : ℕ → ℕ) (y : ℝ),
    binaryDigits d →
    awayFromBinaryAmbiguity d →
    y = binaryValue d →
    Summable (fun j : ℕ =>
      if 0 < j then (j : ℝ) * (d j : ℝ) / (2 : ℝ) ^ j else 0) ∧
      Summable (fun i : ℕ =>
        realFractionalPart ((2 : ℝ) ^ i * y) / (2 : ℝ) ^ i) ∧
      binaryMoment d = rhoTwo y

def terminatingBinaryExpansion (p : ℕ) (u : ℕ → ℝ) (j : ℕ) : ℝ :=
  if 0 < j ∧ j < p then u j else if j = p then 1 else 0

def allOnesBinaryExpansion (p : ℕ) (u : ℕ → ℝ) (j : ℕ) : ℝ :=
  if 0 < j ∧ j < p then u j else if j = p then 0 else if p < j then 1 else 0

def binaryPrefix (p : ℕ) (u : ℕ → ℝ) : Prop :=
  ∀ j, 0 < j → j < p → u j = 0 ∨ u j = 1

def claim44261 : Prop :=
  ∀ (p : ℕ), 0 < p →
    ∀ u : ℕ → ℝ,
      binaryPrefix p u →
      (Summable (fun j : ℕ => terminatingBinaryExpansion p u j / (2 : ℝ) ^ j) ∧
        Summable (fun j : ℕ => allOnesBinaryExpansion p u j / (2 : ℝ) ^ j) ∧
        Summable (fun j : ℕ =>
          (j : ℝ) * terminatingBinaryExpansion p u j / (2 : ℝ) ^ j) ∧
        Summable (fun j : ℕ =>
          (j : ℝ) * allOnesBinaryExpansion p u j / (2 : ℝ) ^ j)) ∧
      realBinaryValue (terminatingBinaryExpansion p u) =
        realBinaryValue (allOnesBinaryExpansion p u) ∧
      realBinaryMoment (allOnesBinaryExpansion p u) -
          realBinaryMoment (terminatingBinaryExpansion p u) =
        2 / (2 : ℝ) ^ p

end BinaryArithmetic

end

end MathlibPlus.Open.ResearchFormalizationBatch
