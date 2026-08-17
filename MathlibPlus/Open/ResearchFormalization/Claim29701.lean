import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim29701

universe u

noncomputable section
open Classical

/-- A concrete multiplicative model of `C₃²`. -/
abbrev C3SquareGroup := Multiplicative (ZMod 3 × ZMod 3)

/-- Concrete cyclic models used by the two sharpness counterexamples. -/
abbrev C3Group := Multiplicative (ZMod 3)
abbrev C2Group := Multiplicative (ZMod 2)

/-- The inverse pair containing a nonidentity element. -/
def inversePair (x : C3SquareGroup) : Finset C3SquareGroup :=
  {x, x⁻¹}

def nonidentityElements : Finset C3SquareGroup :=
  Finset.univ.filter (fun x : C3SquareGroup => x ≠ 1)

def inversePairs : Finset (Finset C3SquareGroup) :=
  nonidentityElements.image inversePair

/-- A support chooses at most one member from each inverse pair and excludes
zero (the identity in the multiplicative model). -/
def inversePairSeparated (C : Finset C3SquareGroup) : Prop :=
  ∀ x ∈ C, x ≠ 1 ∧ x⁻¹ ∉ C

def separatedSupports : Finset (Finset C3SquareGroup) :=
  Finset.univ.filter inversePairSeparated

def nonemptySeparatedSupports : Finset (Finset C3SquareGroup) :=
  separatedSupports.filter Finset.Nonempty

/-- The fibre permutation map used by the set-fixing assertion. -/
def fiberMap {A H : Type*} (q : H → Equiv.Perm A) : A × H → A × H :=
  fun p => (q p.2 p.1, p.2)

def activeSupport {A H : Type*} [Group H]
    (q : H → Equiv.Perm A) : Set H :=
  {h | q h ≠ 1}

def inverseClosed {G : Type*} [Group G] (S : Set G) : Prop :=
  ∀ x : G, x ∈ S ↔ x⁻¹ ∈ S

/-- Every separated support on `C₃²` gives the set-fixing conclusion for
arbitrary finite fibre groups and arbitrary permutations on the support. -/
def separatedFiberPermutationsAreHarmless
    (C : Finset C3SquareGroup) (A : Type u) [Fintype A] [Group A]
    (q : C3SquareGroup → Equiv.Perm A) : Prop :=
  activeSupport q = (C : Set C3SquareGroup) →
    ∀ S : Set (A × C3SquareGroup),
      inverseClosed S →
      inverseClosed (fiberMap q '' S) →
      fiberMap q '' S = S

/-- The transposition of the two elements of the cyclic group `C₂`. -/
def c2Nonidentity : C2Group :=
  Multiplicative.ofAdd (1 : ZMod 2)

def c2Swap : Equiv.Perm C2Group :=
  Equiv.swap (1 : C2Group) c2Nonidentity

/-- Swapping both nonidentity inverse fibres over `C₃`. -/
def qBothNonidentityC3 : C3Group → Equiv.Perm C2Group :=
  fun h => if h = 1 then 1 else c2Swap

def c3Nonidentity : C3Group :=
  Multiplicative.ofAdd (1 : ZMod 3)

def c3MovedSet : Set (C2Group × C3Group) :=
  {(1, c3Nonidentity), (1, c3Nonidentity⁻¹)}

def c3SharpFailure : Prop :=
  activeSupport qBothNonidentityC3 = {h : C3Group | h ≠ 1} ∧
    (∀ h : C3Group, h ≠ 1 → qBothNonidentityC3 h = c2Swap) ∧
    inverseClosed c3MovedSet ∧
    inverseClosed (fiberMap qBothNonidentityC3 '' c3MovedSet) ∧
    fiberMap qBothNonidentityC3 '' c3MovedSet ≠ c3MovedSet

/-- Activating the self-inverse nonidentity fibre over `C₂`. -/
def qSelfInverseC2 : C2Group → Equiv.Perm C2Group :=
  fun h => if h = c2Nonidentity then c2Swap else 1

def c2MovedSet : Set (C2Group × C2Group) :=
  {(1, c2Nonidentity)}

def c2SharpFailure : Prop :=
  c2Nonidentity⁻¹ = c2Nonidentity ∧
    activeSupport qSelfInverseC2 = {c2Nonidentity} ∧
    qSelfInverseC2 c2Nonidentity = c2Swap ∧
    inverseClosed c2MovedSet ∧
    inverseClosed (fiberMap qSelfInverseC2 '' c2MovedSet) ∧
    fiberMap qSelfInverseC2 '' c2MovedSet ≠ c2MovedSet

/-- Claim 29701: the four inverse pairs, the `3⁴ = 81` separated supports,
all nonempty-support and size bounds, the harmless separated-support action,
and the two explicit set-fixing sharpness failures are retained.  The claim
ends at set fixing and asserts no CI-defect predicate for either example. -/
def claim29701 : Prop :=
  Fintype.card {x : C3SquareGroup // x ≠ 1} = 8 ∧
    inversePairs.card = 4 ∧
    (∀ P ∈ inversePairs, P.card = 2) ∧
    separatedSupports.card = 3 ^ 4 ∧
    separatedSupports.card = 81 ∧
    nonemptySeparatedSupports.card = 80 ∧
    (∀ C ∈ separatedSupports, C.card ≤ 4) ∧
    (∀ (C : Finset C3SquareGroup), C ∈ separatedSupports →
      ∀ (A : Type u) [Fintype A] [Group A]
        (q : C3SquareGroup → Equiv.Perm A),
        separatedFiberPermutationsAreHarmless C A q) ∧
    c3SharpFailure ∧
    c2SharpFailure

end

end MathlibPlus.Open.ResearchFormalization.Claim29701
