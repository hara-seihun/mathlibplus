import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

noncomputable section
open Classical

/-! Exact finite carriers for the two census claims. -/

abbrev C4C3 := ZMod 4 × (Fin 3 → ZMod 3)

def inverseAtom (x : C4C3) : Finset C4C3 := {x, -x}

def InverseAtom : Type :=
  {s : Finset C4C3 // ∃ x : C4C3, x ≠ 0 ∧ s = inverseAtom x}

def InverseClosedConnectionSet : Type :=
  {s : Finset C4C3 // 0 ∉ s ∧ ∀ x : C4C3, x ∈ s ↔ -x ∈ s}

deriving instance Fintype for InverseAtom
deriving instance Fintype for InverseClosedConnectionSet

/-- Claim 55624: the inverse atoms, inverse-closed connection sets, and automorphism
cardinalities for `C_4 × C_3^3`. -/
def claim_55624 : Prop :=
  Fintype.card InverseAtom = 54 ∧
    Fintype.card InverseClosedConnectionSet = 2 ^ 54 ∧
    Fintype.card (C4C3 ≃+ C4C3) = 22464

/-- Two inverse-closed connection sets are in the same automorphism orbit. -/
def sameAutOrbit (S T : InverseClosedConnectionSet) : Prop :=
  ∃ e : C4C3 ≃+ C4C3,
    ∀ x : C4C3, x ∈ S.1 ↔ e x ∈ T.1

def generatesC4C3 (S : InverseClosedConnectionSet) : Prop :=
  AddSubgroup.closure (S.1 : Set C4C3) = ⊤

/-- A finite representative family has exactly one member of each orbit satisfying
`P`; the coverage and separation clauses make the representative witness
non-arbitrary. -/
def hasOrbitRepresentatives
    (P : InverseClosedConnectionSet → Prop)
    (reps : Finset InverseClosedConnectionSet)
    (n : Nat) : Prop :=
  reps.card = n ∧
    (∀ S, P S → ∃ R, R ∈ reps ∧ sameAutOrbit S R) ∧
    (∀ R, R ∈ reps → P R) ∧
    (∀ R₁, R₁ ∈ reps → ∀ R₂, R₂ ∈ reps →
      sameAutOrbit R₁ R₂ → R₁ = R₂)

/-- Claim 55625: exact total, generating, and nongenerating automorphism-orbit
censuses, with the concrete finite group and connection-set carriers above. -/
def claim_55625 : Prop :=
  ∃ total generating nongenerating : Finset InverseClosedConnectionSet,
    hasOrbitRepresentatives
      (fun _ : InverseClosedConnectionSet => True)
      total 1605663037888 ∧
    hasOrbitRepresentatives generatesC4C3 generating 1605662993566 ∧
    hasOrbitRepresentatives
      (fun S : InverseClosedConnectionSet => ¬ generatesC4C3 S)
      nongenerating 44322

/-! The shared-pointer finite cube.  Coordinates are ordered
`(A_0,A_1,B_1^0,B_1^1,B_2^0,B_2^1,Z_0,Z_1)`. -/

abbrev PointerInput := Fin 8 → Bool

def chooseBit (b v0 v1 : Bool) : Bool :=
  match b with
  | false => v0
  | true => v1

def pointerT0 (x : PointerInput) : Bool :=
  let b1 := chooseBit (x 0) (x 2) (x 3)
  let b2 := chooseBit b1 (x 4) (x 5)
  chooseBit b2 (x 6) (x 7)

def pointerT1 (x : PointerInput) : Bool :=
  let b1 := chooseBit (x 1) (x 2) (x 3)
  let b2 := chooseBit b1 (x 4) (x 5)
  chooseBit b2 (x 6) (x 7)

def boolSign (b : Bool) : ℚ :=
  match b with
  | false => -1
  | true => 1

def pointerG (x : PointerInput) : ℚ :=
  (boolSign (pointerT0 x) + boolSign (pointerT1 x)) / 2

def PointerCompletion : Type :=
  {h : PointerInput → Bool //
    ∀ x : PointerInput,
      pointerT0 x = pointerT1 x → boolSign (h x) = pointerG x}

/-- Claim 55676: the two-layer shared-pointer construction has 16 disagreement
inputs, 240 forced inputs, and exactly `2^16` Boolean completions. -/
def claim_55676 : Prop :=
  Fintype.card PointerInput = 256 ∧
    Fintype.card {x : PointerInput // pointerT0 x ≠ pointerT1 x} = 16 ∧
    Fintype.card {x : PointerInput // pointerT0 x = pointerT1 x} = 240 ∧
    Nat.card PointerCompletion = 2 ^ 16

/-! A direct deterministic query-tree carrier for the convex-roof statement. -/

inductive QueryTree (ι : Type*) where
  | leaf : Bool → QueryTree ι
  | query : ι → QueryTree ι → QueryTree ι → QueryTree ι

def QueryTree.eval : QueryTree ι → (ι → Bool) → Bool
  | .leaf b, _ => b
  | .query i left right, x =>
      match x i with
      | false => QueryTree.eval left x
      | true => QueryTree.eval right x

def QueryTree.cost : QueryTree ι → (ι → Bool) → Nat
  | .leaf _, _ => 0
  | .query i left right, x =>
      1 + match x i with
        | false => QueryTree.cost left x
        | true => QueryTree.cost right x

def realizes (t : QueryTree (Fin 8)) (f : PointerInput → Bool) : Prop :=
  ∀ x : PointerInput, t.eval x = f x

def uniformExpectedCost (t : QueryTree (Fin 8)) : ℚ :=
  (∑ x : PointerInput, (t.cost x : ℚ)) / Fintype.card PointerInput

def hasMinimumQueryCost (f : PointerInput → Bool) (q : ℚ) : Prop :=
  (∀ t, realizes t f → q ≤ uniformExpectedCost t) ∧
    ∃ t, realizes t f ∧ uniformExpectedCost t = q

def uniformMean (f : PointerInput → ℚ) : ℚ :=
  (∑ x : PointerInput, f x) / Fintype.card PointerInput

def booleanMean (f : PointerInput → Bool) : ℚ :=
  uniformMean (fun x => boolSign (f x))

def booleanCovariance
    (f g : PointerInput → Bool) : ℚ :=
  uniformMean (fun x => boolSign (f x) * boolSign (g x)) -
    booleanMean f * booleanMean g

def uniformVariance (f : PointerInput → ℚ) : ℚ :=
  uniformMean (fun x => (f x - uniformMean f) ^ 2)

def PointerBoolean := PointerInput → Bool

deriving instance Fintype for PointerBoolean

 def isConvexRepresentation (w : PointerBoolean → ℚ) : Prop :=
  (∀ f, 0 ≤ w f) ∧
    (∑ f : PointerBoolean, w f) = 1 ∧
    (∀ x : PointerInput,
      pointerG x = ∑ f : PointerBoolean, w f * boolSign (f x))

def displayedWeight (f : PointerBoolean) : ℚ :=
  if f = pointerT0 then 1 / 2
  else if f = pointerT1 then 1 / 2
  else 0

/-- Claim 55677: the exact query-cost lower bound, the displayed two-atom
convex-roof optimum, and the stated covariance/variance values.  The cost
function is constrained to be the minimum over the explicit query-tree carrier,
so the quantified cost assignment is not an unconstrained certificate. -/
def claim_55677 : Prop :=
  ∃ q : PointerBoolean → ℚ,
    (∀ f, hasMinimumQueryCost f (q f)) ∧
    q pointerT0 = 7 / 2 ∧
    q pointerT1 = 7 / 2 ∧
    (∀ h : PointerCompletion, ∀ t,
      realizes t h.1 → 7 / 2 ≤ uniformExpectedCost t) ∧
    isConvexRepresentation displayedWeight ∧
    (∑ f : PointerBoolean, displayedWeight f * q f) = 7 / 2 ∧
    (∀ w : PointerBoolean → ℚ,
      isConvexRepresentation w →
        7 / 2 ≤ ∑ f : PointerBoolean, w f * q f) ∧
    booleanMean pointerT0 = 0 ∧
    booleanMean pointerT1 = 0 ∧
    booleanCovariance pointerT0 pointerT1 = 7 / 8 ∧
    uniformVariance pointerG = (1 + 7 / 8) / 2 ∧
    uniformVariance pointerG = 15 / 16

end

end MathlibPlus.Open.ResearchFormalization
