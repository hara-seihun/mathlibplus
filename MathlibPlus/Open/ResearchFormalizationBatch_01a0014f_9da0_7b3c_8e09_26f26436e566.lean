import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalizationBatch

abbrev Sign := Bool

instance signFintype : Fintype Sign := inferInstanceAs (Fintype Bool)

noncomputable instance signInputFintype (α : Type*) [Fintype α] : Fintype (α → Sign) :=
  Fintype.ofFinite _

def negSign : Sign := false

def posSign : Sign := true

/-- Multiplication of signs, with `false` denoting `-1` and `true` denoting `+1`. -/
def signProduct (a b : Sign) : Sign := decide (a = b)

/-- The real value represented by a sign. -/
def signReal (s : Sign) : ℝ := if s = posSign then 1 else -1

abbrev BooleanFunction (α : Type*) := (α → Sign) → Sign

inductive DecisionTree (α : Type*) where
  | leaf (value : Sign)
  | query (coordinate : α) (negative positive : DecisionTree α)

namespace DecisionTree

def evaluate : DecisionTree α → (α → Sign) → Sign
  | .leaf value, _ => value
  | .query coordinate negative positive, input =>
      match input coordinate with
      | false => evaluate negative input
      | true => evaluate positive input

def queryCount : DecisionTree α → (α → Sign) → Nat
  | .leaf _, _ => 0
  | .query coordinate negative positive, input =>
      match input coordinate with
      | false => 1 + queryCount negative input
      | true => 1 + queryCount positive input

def queried : DecisionTree α → α → (α → Sign) → Prop
  | .leaf _, _, _ => False
  | .query coordinate negative positive, target, input =>
      coordinate = target ∨
        match input coordinate with
        | false => queried negative target input
        | true => queried positive target input

end DecisionTree

def Computes (tree : DecisionTree α) (f : BooleanFunction α) : Prop :=
  ∀ input, tree.evaluate input = f input

noncomputable def expectedQueries [Fintype α] (tree : DecisionTree α) : ℝ :=
  (∑ input : α → Sign, (tree.queryCount input : ℝ)) /
    (Fintype.card (α → Sign) : ℝ)

/-- The minimum expected query count under the uniform sign distribution. -/
noncomputable def q [Fintype α] (f : BooleanFunction α) : ℝ :=
  sInf {value : ℝ | ∃ tree : DecisionTree α, Computes tree f ∧ value = expectedQueries tree}

def IsNonconstant (f : BooleanFunction α) : Prop :=
  ∃ input₁ input₂, f input₁ ≠ f input₂

def constantFunction (α : Type*) (value : Sign) : BooleanFunction α :=
  fun _ => value

abbrev Remaining (α : Type*) (coordinate : α) := {j : α // j ≠ coordinate}

def restrictCoordinate [DecidableEq α] (f : BooleanFunction α) (coordinate : α)
    (value : Sign) : BooleanFunction (Remaining α coordinate) :=
  fun input => f (fun j => if h : j = coordinate then value else input ⟨j, h⟩)

noncomputable def intrinsicSaving [Fintype α] [DecidableEq α] (f : BooleanFunction α)
    (coordinate : α) : ℝ :=
  q f - (q (restrictCoordinate f coordinate negSign) +
    q (restrictCoordinate f coordinate posSign)) / 2

noncomputable def totalSaving [Fintype α] [DecidableEq α] (f : BooleanFunction α) : ℝ :=
  ∑ coordinate : α, intrinsicSaving f coordinate

noncomputable def IsMinimumExpectedQueryTree [Fintype α] (f : BooleanFunction α) : Prop :=
  ∃ tree : DecisionTree α,
    Computes tree f ∧ expectedQueries tree = q f ∧
      ∀ other : DecisionTree α, Computes other f → expectedQueries tree ≤ expectedQueries other

/-- Claim 50321: query complexity and coordinate savings under uniform signs. -/
def claim50321 : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (f : BooleanFunction α),
    IsNonconstant f →
      IsMinimumExpectedQueryTree f ∧
      (∀ coordinate : α,
        intrinsicSaving f coordinate =
          q f - (q (restrictCoordinate f coordinate negSign) +
            q (restrictCoordinate f coordinate posSign)) / 2) ∧
      totalSaving f = ∑ coordinate : α, intrinsicSaving f coordinate

/-- The all-positive atom on a finite sign-coordinate type. -/
def allPositive [Fintype α] (input : α → Sign) : Sign :=
  if h : ∀ coordinate, input coordinate = posSign then posSign else negSign

def a (r : Nat) : BooleanFunction (Fin r) := allPositive

/-- Claim 50327: sequential query complexity and the two coordinate restrictions. -/
def claim50327 : Prop :=
  ∀ r : Nat,
    q (a r) = 2 * (1 - (2 : ℝ)⁻¹ ^ r) ∧
    ∀ coordinate : Fin r,
      restrictCoordinate (a r) coordinate negSign =
          constantFunction (Remaining (Fin r) coordinate) negSign ∧
      restrictCoordinate (a r) coordinate posSign =
          allPositive ∧
      intrinsicSaving (a r) coordinate = 1

/-- Add a fresh sign coordinate and multiply a Boolean function by it. -/
def withFresh (f : BooleanFunction α) : BooleanFunction (Sum α Unit) :=
  fun input => signProduct (input (Sum.inr ()))
    (f (fun coordinate => input (Sum.inl coordinate)))

def freshCoordinate : Sum α Unit := Sum.inr ()

def oldCoordinate (coordinate : α) : Sum α Unit := Sum.inl coordinate

abbrev TwoBlocks (r : Nat) := Sum (Sum (Fin r) (Fin r)) Unit

abbrev BlockCore (r : Nat) := Sum (Fin r) (Fin r)

def xAtom (r : Nat) : BooleanFunction (BlockCore r) :=
  fun input => allPositive (fun coordinate => input (Sum.inl coordinate))

def uAtom (r : Nat) : BooleanFunction (BlockCore r) :=
  fun input => allPositive (fun coordinate => input (Sum.inr coordinate))

def hAtom (r : Nat) : BooleanFunction (TwoBlocks r) := withFresh (xAtom r)

def uAtomFresh (r : Nat) : BooleanFunction (TwoBlocks r) := withFresh (uAtom r)

def xCoordinate (r : Nat) (coordinate : Fin r) : TwoBlocks r :=
  Sum.inl (Sum.inl coordinate)

def yCoordinate (r : Nat) (coordinate : Fin r) : TwoBlocks r :=
  Sum.inl (Sum.inr coordinate)

def zCoordinate (r : Nat) : TwoBlocks r := Sum.inr ()

def xSupport (r : Nat) : Finset (TwoBlocks r) :=
  Finset.image (xCoordinate r) Finset.univ

def ySupport (r : Nat) : Finset (TwoBlocks r) :=
  Finset.image (yCoordinate r) Finset.univ

def hSupport (r : Nat) : Finset (TwoBlocks r) :=
  insert (zCoordinate r) (xSupport r)

def uSupport (r : Nat) : Finset (TwoBlocks r) :=
  insert (zCoordinate r) (ySupport r)

def finsetIndicator [DecidableEq α] (support : Finset α) (coordinate : α) : ℝ :=
  if coordinate ∈ support then 1 else 0

noncomputable def savingDotProduct [Fintype α] [DecidableEq α]
    (f g : BooleanFunction α) : ℝ :=
  ∑ coordinate : α, intrinsicSaving f coordinate * intrinsicSaving g coordinate

/-- Claim 50331: the fresh-coordinate identities and the two disjoint-block atoms. -/
def claim50331 : Prop :=
  (∀ (α : Type) [Fintype α] [DecidableEq α] (f : BooleanFunction α),
    (∀ tree : DecisionTree (Sum α Unit), Computes tree (withFresh f) →
      ∀ input, tree.queried (freshCoordinate : Sum α Unit) input) ∧
    q (withFresh f) = 1 + q f ∧
    (∀ coordinate : α,
      intrinsicSaving (withFresh f) (oldCoordinate coordinate) =
        intrinsicSaving f coordinate) ∧
    intrinsicSaving (withFresh f) (freshCoordinate : Sum α Unit) = 1) ∧
  (∀ r : Nat,
    (∀ coordinate : TwoBlocks r,
      intrinsicSaving (hAtom r) coordinate =
        finsetIndicator (hSupport r) coordinate) ∧
    (∀ coordinate : TwoBlocks r,
      intrinsicSaving (uAtomFresh r) coordinate =
        finsetIndicator (uSupport r) coordinate) ∧
    totalSaving (hAtom r) = ((r + 1 : Nat) : ℝ) ∧
    totalSaving (uAtomFresh r) = ((r + 1 : Nat) : ℝ) ∧
    savingDotProduct (hAtom r) (uAtomFresh r) = 1)

noncomputable def uniformExpectation [Fintype α] (value : α → ℝ) : ℝ :=
  (∑ input : α, value input) / (Fintype.card α : ℝ)

noncomputable def signMean [Fintype α] (f : BooleanFunction α) : ℝ :=
  uniformExpectation (fun input => signReal (f input))

noncomputable def covariance [Fintype α] (f g : BooleanFunction α) : ℝ :=
  let meanF := signMean f
  let meanG := signMean g
  uniformExpectation (fun input =>
    (signReal (f input) - meanF) * (signReal (g input) - meanG))

noncomputable def proposedBound (r : Nat) : ℝ := 2 / ((r + 1 : Nat) : ℝ)

/-- Claim 50334: centering, covariance, its strict comparison, and the r=3 values. -/
def claim50334 : Prop :=
  (∀ r : Nat,
    signMean (hAtom r) = 0 ∧
    signMean (uAtomFresh r) = 0 ∧
    signMean (a r) = (2 : ℝ) ^ (1 - (r : ℤ)) - 1 ∧
    covariance (hAtom r) (uAtomFresh r) =
      (1 - (2 : ℝ) ^ (1 - (r : ℤ))) ^ 2 ∧
    (3 ≤ r →
      (1 - (2 : ℝ) ^ (1 - (r : ℤ))) ^ 2 > proposedBound r)) ∧
  q (hAtom 3) = 11 / 4 ∧
  q (uAtomFresh 3) = 11 / 4 ∧
  covariance (hAtom 3) (uAtomFresh 3) = 9 / 16 ∧
  proposedBound 3 = 1 / 2

end MathlibPlus.Open.ResearchFormalizationBatch
