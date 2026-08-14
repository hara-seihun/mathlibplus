import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch019ffee1

/-- The literal support of a ground coordinate in a finite indexed family. -/
def incidenceSupport {α : Type} [DecidableEq α] {m : Nat}
    (A : Fin m → Finset α) (x : α) : Finset (Fin m) :=
  (Finset.univ : Finset (Fin m)).filter (fun i => x ∈ A i)

/-- The actual ground coordinates occurring in a finite family. -/
def groundCoordinates {α : Type} [DecidableEq α] {m : Nat}
    (A : Fin m → Finset α) : Finset α :=
  (Finset.univ : Finset (Fin m)).biUnion A

/-- The distinct nonempty literal incidence supports. -/
def supportFamily {α : Type} [DecidableEq α] {m : Nat}
    (A : Fin m → Finset α) : Finset (Finset (Fin m)) :=
  (groundCoordinates A).biUnion (fun x => {incidenceSupport A x})

 def memberUniform {α : Type} [DecidableEq α] {m : Nat}
    (A : Fin m → Finset α) (n : Nat) : Prop :=
  ∀ i, (A i).card = n

 def supportUnionClosed {m : Nat} (S : Finset (Finset (Fin m))) : Prop :=
  ∀ U ∈ S, ∀ V ∈ S, U ∪ V ∈ S

 def supportSeparating {m : Nat} (S : Finset (Finset (Fin m))) : Prop :=
  ∀ i j : Fin m, i ≠ j →
    ∃ U ∈ S, (i ∈ U ∧ j ∉ U) ∨ (j ∈ U ∧ i ∉ U)

 def supportMultiplicity {α : Type} [DecidableEq α] {m : Nat}
    (A : Fin m → Finset α) (U : Finset (Fin m)) : Nat :=
  ((groundCoordinates A).filter (fun x => incidenceSupport A x = U)).card

 def positiveSupportMultiplicities {α : Type} [DecidableEq α] {m : Nat}
    (A : Fin m → Finset α) : Prop :=
  ∀ U ∈ supportFamily A, 0 < supportMultiplicity A U

/-- Literal incidence supports, with distinct uniform members and union closure. -/
def literalIncidenceSupportSemilattice {α : Type} [DecidableEq α]
    (m n : Nat) (A : Fin m → Finset α) : Prop :=
  1 ≤ n ∧
  memberUniform A n ∧
  Function.Injective A ∧
  supportSeparating (supportFamily A) ∧
  supportUnionClosed (supportFamily A) ∧
  positiveSupportMultiplicities A

 def supportFrequency {m : Nat} (S : Finset (Finset (Fin m))) (i : Fin m) : Nat :=
  (S.filter (fun U => i ∈ U)).card

/-- Every separating union-closed family on an m-element index set has at least m members. -/
def separatingUnionClosedSupportTheorem : Prop :=
  ∀ (m : Nat) (S : Finset (Finset (Fin m))),
    supportSeparating S → supportUnionClosed S → m ≤ S.card

/-- The golden-ratio frequency charge and its incidence consequence. -/
def goldenRatioIncidenceCharge : Prop :=
  ∀ {α : Type} [DecidableEq α] (m n : Nat) (A : Fin m → Finset α),
    1 ≤ n →
    memberUniform A n →
    Function.Injective A →
    supportUnionClosed (supportFamily A) →
    supportSeparating (supportFamily A) ∧
      positiveSupportMultiplicities A ∧
      (∃ i : Fin m,
        ((3 - Real.sqrt 5) / 2) * (supportFamily A).card ≤
          (supportFrequency (supportFamily A) i : ℝ)) ∧
      m ≤ (supportFamily A).card ∧
      (m : ℝ) ≤ ((3 + Real.sqrt 5) / 2) * (n : ℝ)

/-- The unconditional incidence bound for distinct uniform families in this support class. -/
def unionClosedSupportTheorem : Prop :=
  ∀ {α : Type} [DecidableEq α] (m n : Nat) (A : Fin m → Finset α),
    1 ≤ n →
    memberUniform A n →
    Function.Injective A →
    supportUnionClosed (supportFamily A) →
    (m : ℝ) ≤ ((3 + Real.sqrt 5) / 2) * (n : ℝ)

/-- All nonempty subsets of [p], represented as the ground coordinates. -/
def booleanGround (p : Nat) : Finset (Finset (Fin p)) :=
  (Finset.univ : Finset (Finset (Fin p))).filter (fun S => S.Nonempty)

/-- The member of the Boolean support fixture indexed by i. -/
def booleanMember (p : Nat) (i : Fin p) : Finset (Finset (Fin p)) :=
  (booleanGround p).filter (fun S => i ∈ S)

/-- The full crossing Boolean support fixture, including its uniformity claim. -/
def basicHighlyCrossingBooleanSupportFixture (p : Nat) : Prop :=
  1 ≤ p ∧
  (∀ i : Fin p, (booleanMember p i).card = 2 ^ (p - 1)) ∧
  Function.Injective (booleanMember p) ∧
  (∀ S ∈ booleanGround p,
    incidenceSupport (booleanMember p) S = S) ∧
  supportFamily (booleanMember p) = booleanGround p ∧
  supportSeparating (supportFamily (booleanMember p)) ∧
  supportUnionClosed (supportFamily (booleanMember p)) ∧
  (2 ≤ p →
    ∃ S T : Finset (Fin p),
      S ∈ supportFamily (booleanMember p) ∧
      T ∈ supportFamily (booleanMember p) ∧
      ¬ S ⊆ T ∧ ¬ T ⊆ S)

/-- Repeating every support pattern by a positive multiplicity depending only on its size. -/
def weightedBooleanMember (p : Nat) (μ : Finset (Fin p) → Nat) (i : Fin p) :
    Finset (Σ S : Finset (Fin p), Fin (μ S)) :=
  (Finset.univ : Finset (Σ S : Finset (Fin p), Fin (μ S))).filter
    (fun z => i ∈ z.1)

def weightedBooleanSupportFixture (p : Nat) : Prop :=
  ∀ μ : Finset (Fin p) → Nat,
    μ ∅ = 0 →
    (∀ S : Finset (Fin p), S.Nonempty → 0 < μ S) →
    (∀ S T : Finset (Fin p), S.card = T.card → μ S = μ T) →
    (∀ i j : Fin p,
      (weightedBooleanMember p μ i).card =
        (weightedBooleanMember p μ j).card) ∧
    (∀ (S : Finset (Fin p)) (k : Fin (μ S)),
      incidenceSupport (weightedBooleanMember p μ) ⟨S, k⟩ = S) ∧
    supportFamily (weightedBooleanMember p μ) = booleanGround p ∧
    supportUnionClosed (supportFamily (weightedBooleanMember p μ))

/-- The complete Boolean fixture, including the positive size-dependent multiplicity variant. -/
def highlyCrossingBooleanSupportFixture (p : Nat) : Prop :=
  basicHighlyCrossingBooleanSupportFixture p ∧
  weightedBooleanSupportFixture p

/-- A concrete planar point representation used for the endpoint replacement claim. -/
abbrev Point := ℝ × ℝ

def pointAdd (x y : Point) : Point := (x.1 + y.1, x.2 + y.2)
def pointSub (x y : Point) : Point := (x.1 - y.1, x.2 - y.2)
def pointScale (r : ℝ) (x : Point) : Point := (r * x.1, r * x.2)
def pointDot (x y : Point) : ℝ := x.1 * y.1 + x.2 * y.2
def pointSqNorm (x : Point) : ℝ := pointDot x x

def endpointPoint (u v : Point) (z : ℤ × ℤ) : Point :=
  pointAdd (pointScale (z.1 : ℝ) u) (pointScale (z.2 : ℝ) v)

def endpointConfiguration (u v : Point) (S : Finset (ℤ × ℤ)) : Set Point :=
  {x | ∃ z ∈ S, x = endpointPoint u v z}

def endpointDifferenceSet (S : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  S.biUnion (fun x => S.image (fun y => (x.1 - y.1, x.2 - y.2)))

def endpointQ (ρ : ℝ) (a b : ℤ) : ℝ :=
  (a : ℝ) ^ 2 + (b : ℝ) ^ 2 + 2 * ρ * (a : ℝ) * (b : ℝ)

noncomputable def endpointDiameterSq (ρ : ℝ) (S : Finset (ℤ × ℤ)) : ℝ :=
  sSup {r : ℝ | ∃ z ∈ endpointDifferenceSet S, r = endpointQ ρ z.1 z.2}

noncomputable def endpointDiameter (ρ : ℝ) (S : Finset (ℤ × ℤ)) : ℝ :=
  Real.sqrt (endpointDiameterSq ρ S)

def endpointUnitSeparated (u v : Point) (S : Finset (ℤ × ℤ)) : Prop :=
  ∀ z ∈ S, ∀ z' ∈ S, z ≠ z' →
    1 ≤ pointSqNorm (pointSub (endpointPoint u v z) (endpointPoint u v z'))

def endpointUnitGraphBipartite (u v : Point) (S : Finset (ℤ × ℤ)) : Prop :=
  ∃ color : {x // x ∈ endpointConfiguration u v S} → Bool,
    ∀ x y : {x // x ∈ endpointConfiguration u v S},
      pointSqNorm (pointSub x.1 y.1) = 1 →
      color x ≠ color y

def endpointUnitGraphTriangleFree (u v : Point) (S : Finset (ℤ × ℤ)) : Prop :=
  ∀ x y z : {x // x ∈ endpointConfiguration u v S},
    x ≠ y → y ≠ z → x ≠ z →
    ¬ (pointSqNorm (pointSub x.1 y.1) = 1 ∧
       pointSqNorm (pointSub y.1 z.1) = 1 ∧
       pointSqNorm (pointSub x.1 z.1) = 1)

/-- The fixed-index endpoint replacement statement, including both endpoint directions. -/
def fixedIndexEndpointReplacementTheorem : Prop :=
  ∀ (S : Finset (ℤ × ℤ)), S.Nonempty →
    (∀ (ρ : ℝ) (u v : Point),
      -(1 : ℝ) / 2 ≤ ρ → ρ ≤ (1 : ℝ) / 2 →
      pointSqNorm u = 1 → pointSqNorm v = 1 → pointDot u v = ρ →
      endpointUnitSeparated u v S) ∧
    (∀ (ρ : ℝ) (u v : Point),
      -(1 : ℝ) / 2 < ρ → ρ < (1 : ℝ) / 2 →
      pointSqNorm u = 1 → pointSqNorm v = 1 → pointDot u v = ρ →
      endpointUnitGraphBipartite u v S ∧
      endpointUnitGraphTriangleFree u v S) ∧
    (∀ (a b : ℤ),
      (a, b) ∈ endpointDifferenceSet S →
      (a : ℤ) * b < 0 →
      endpointQ (1 / 2 : ℝ) a b = endpointDiameterSq (1 / 2 : ℝ) S →
      ∀ ρ : ℝ, -(1 : ℝ) / 2 < ρ → ρ < (1 : ℝ) / 2 →
        endpointQ ρ a b =
          endpointQ (1 / 2 : ℝ) a b +
            2 * ((1 : ℝ) / 2 - ρ) * |(a : ℝ) * (b : ℝ)| ∧
        endpointDiameter ρ S > endpointDiameter (1 / 2 : ℝ) S) ∧
    (∀ (a b : ℤ),
      (a, b) ∈ endpointDifferenceSet S →
      0 < (a : ℤ) * b →
      endpointQ (-1 / 2 : ℝ) a b = endpointDiameterSq (-1 / 2 : ℝ) S →
      ∀ ρ : ℝ, -(1 : ℝ) / 2 < ρ → ρ < (1 : ℝ) / 2 →
        endpointQ ρ a b =
          endpointQ (-1 / 2 : ℝ) a b +
            2 * (ρ + (1 : ℝ) / 2) * |(a : ℝ) * (b : ℝ)| ∧
        endpointDiameter ρ S > endpointDiameter (-1 / 2 : ℝ) S)

noncomputable def blockerT (m : Nat) : ℝ :=
  1 / Real.sqrt 3 - 1 / (m : ℝ)

noncomputable def blockerW (m : Nat) : Point :=
  ((1 - blockerT m ^ 2) / (1 + blockerT m ^ 2),
    2 * blockerT m / (1 + blockerT m ^ 2))

noncomputable def blockerV : Point := (-1 / 2, Real.sqrt 3 / 2)
def blockerA : Point := (0, 0)
def blockerB : Point := (1, 0)
noncomputable def blockerRho (m : Nat) : ℝ := pointDot (blockerW m) blockerV

noncomputable def blockerLength (m : Nat) : ℝ := Real.sqrt (2 - 2 * blockerRho m)
noncomputable def blockerN (m : Nat) : Nat := Nat.ceil (2 / (blockerLength m - 1))

noncomputable def blockerZ (m i j : Nat) : Point :=
  pointAdd blockerB
    (pointAdd (pointScale (i : ℝ) (blockerW m))
      (pointScale (j : ℝ) blockerV))

noncomputable def pointRotate (θ : ℝ) (x : Point) : Point :=
  (Real.cos θ * x.1 - Real.sin θ * x.2,
    Real.sin θ * x.1 + Real.cos θ * x.2)

noncomputable def blockerPatchPoint (θ : ℝ) (m i j : Nat) : Point :=
  pointAdd blockerB
    (pointRotate θ
      (pointAdd (pointScale (i : ℝ) (blockerW m))
        (pointScale (j : ℝ) blockerV)))

def blockerPatchIndices (N : Nat) : Set (Nat × Nat) :=
  {p | p.1 + p.2 ≤ N}

noncomputable def blockerVertexSet (m : Nat) : Set (Option (Nat × Nat)) :=
  {x | x = none ∨ ∃ i j, (i, j) ∈ blockerPatchIndices (blockerN m) ∧ x = some (i, j)}

noncomputable def blockerVertexPoint (θ : ℝ) (m : Nat) : Option (Nat × Nat) → Point
  | none => blockerA
  | some p => blockerPatchPoint θ m p.1 p.2

/-- Exact endpoint contacts and the finite negative-angle triangle-free perturbation. -/
def endpointBlockerContactsAndTriangleFreePerturbation : Prop :=
  ∀ m : Nat, 6 ≤ m →
    pointSqNorm (blockerW m) = 1 ∧
    pointSqNorm blockerV = 1 ∧
    0 < pointDot blockerB (blockerW m) ∧
    0 < blockerRho m ∧
    blockerLength m > 1 ∧
    (∀ i j : Nat,
      (i, j) ∈ blockerPatchIndices (blockerN m) →
      pointSqNorm (blockerZ m i j) =
        1 + (i : ℝ) ^ 2 + (j : ℝ) ^ 2 +
          2 * (i : ℝ) * pointDot blockerB (blockerW m) - (j : ℝ) +
          2 * (i : ℝ) * (j : ℝ) * blockerRho m) ∧
    (∀ i j : Nat,
      (i, j) ∈ blockerPatchIndices (blockerN m) →
      pointSqNorm (blockerZ m i j) = 1 ↔
        (i = 0 ∧ j = 0) ∨ (i = 0 ∧ j = 1)) ∧
    pointSqNorm (pointSub blockerA blockerB) = 1 ∧
    (blockerPatchIndices (blockerN m)).Finite ∧
    (blockerVertexSet m).Finite ∧
    (∀ θ : ℝ, ∀ i j i' j' : Nat,
      (i, j) ∈ blockerPatchIndices (blockerN m) →
      (i', j') ∈ blockerPatchIndices (blockerN m) →
      pointSqNorm (pointSub (blockerPatchPoint θ m i j)
        (blockerPatchPoint θ m i' j')) =
        pointSqNorm (pointSub (blockerZ m i j) (blockerZ m i' j'))) ∧
    (HasDerivAt
      (fun θ : ℝ => pointSqNorm
        (pointSub blockerA (blockerPatchPoint θ m 0 1)))
      (-Real.sqrt 3) 0) ∧
    (∃ δ : ℝ, 0 < δ ∧
      ∀ θ : ℝ, -δ < θ → θ < 0 →
        (∀ i j : Nat,
          (i, j) ∈ blockerPatchIndices (blockerN m) →
          (i, j) ≠ (0, 0) →
          pointSqNorm (pointSub blockerA (blockerPatchPoint θ m i j)) > 1) ∧
        (∀ x y z : Option (Nat × Nat),
          x ∈ blockerVertexSet m → y ∈ blockerVertexSet m →
          z ∈ blockerVertexSet m → x ≠ y → y ≠ z → x ≠ z →
          ¬ (pointSqNorm (pointSub (blockerVertexPoint θ m x)
                (blockerVertexPoint θ m y)) = 1 ∧
             pointSqNorm (pointSub (blockerVertexPoint θ m y)
                (blockerVertexPoint θ m z)) = 1 ∧
             pointSqNorm (pointSub (blockerVertexPoint θ m x)
                (blockerVertexPoint θ m z)) = 1)))

end MathlibPlus.Open.ResearchFormalization.Batch019ffee1
