import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResidualNormBatch

abbrev Cube (I : Type*) := I → Bool

/-- The real value represented by a Boolean cube coordinate. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

/-- Expectation for the uniform law on a finite type. -/
def uniformExpectation {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ x, f x) / (Fintype.card α : ℝ)

def uniformL2Squared {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  uniformExpectation (fun x => f x ^ 2)

def uniformVariance {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  let m := uniformExpectation f
  uniformExpectation (fun x => (f x - m) ^ 2)

def centered {α : Type*} (q : α → ℝ) : α → ℝ := fun x => q x - 1

def IsUniformDensity {I : Type*} [Fintype I] [DecidableEq I]
    (q : Cube I → ℝ) : Prop :=
  (∀ x, 0 ≤ q x) ∧ uniformExpectation q = 1

def parity {I : Type*} [DecidableEq I] (S : Finset I) (x : Cube I) : ℝ :=
  ∏ i ∈ S, spin (x i)

/-- A finite coordinate-reveal tree, with a real-valued leaf reward. -/
inductive CoordinateTree (I : Type*) where
  | leaf (value : ℝ)
  | query (coordinate : I)
      (falseBranch : CoordinateTree I) (trueBranch : CoordinateTree I)

def CoordinateTree.eval {I : Type*} : CoordinateTree I → Cube I → ℝ
  | .leaf value, _ => value
  | .query coordinate falseBranch trueBranch, x =>
      if x coordinate then trueBranch.eval x else falseBranch.eval x

def CoordinateTree.height {I : Type*} : CoordinateTree I → ℕ
  | .leaf _ => 0
  | .query _ falseBranch trueBranch =>
      1 + max falseBranch.height trueBranch.height

def CoordinateTree.queried {I : Type*} [DecidableEq I] :
    CoordinateTree I → Finset I
  | .leaf _ => ∅
  | .query coordinate falseBranch trueBranch =>
      insert coordinate (falseBranch.queried ∪ trueBranch.queried)

def CoordinateTree.noRepeated {I : Type*} [DecidableEq I] :
    CoordinateTree I → Prop
  | .leaf _ => True
  | .query coordinate falseBranch trueBranch =>
      falseBranch.noRepeated ∧ trueBranch.noRepeated ∧
        coordinate ∉ falseBranch.queried ∧ coordinate ∉ trueBranch.queried

def HasRevealTree {I : Type*} [Fintype I] [DecidableEq I]
    (q : Cube I → ℝ) (k : ℕ) : Prop :=
  ∃ t : CoordinateTree I,
    t.noRepeated ∧ t.height ≤ k ∧ ∀ x, t.eval x = q x

def fourierCoefficient {I : Type*} [Fintype I] [DecidableEq I]
    (g : Cube I → ℝ) (S : Finset I) : ℝ :=
  uniformExpectation (fun x => g x * parity S x)

def dirichletResource {I : Type*} [Fintype I] [DecidableEq I]
    (g : Cube I → ℝ) : ℝ :=
  ∑ S : Finset I, (S.card : ℝ) * (fourierCoefficient g S) ^ 2

abbrev OtherIndex (I : Type*) (i : I) := {j : I // j ≠ i}

/-- Extend a vector on all coordinates other than `i` by the revealed sign. -/
def extendOther {I : Type*} [DecidableEq I]
    (i : I) (s : Bool) (y : OtherIndex I i → Bool) : Cube I :=
  fun j => if h : j = i then s else y ⟨j, h⟩

def coordinateMass {I : Type*} [Fintype I] [DecidableEq I]
    (q : Cube I → ℝ) (i : I) (s : Bool) : ℝ :=
  uniformExpectation (fun x => if x i = s then q x else 0)

/-- The posterior density relative to the uniform law on the other coordinates. -/
def coordinatePosterior {I : Type*} [Fintype I] [DecidableEq I]
    (q : Cube I → ℝ) (i : I) (s : Bool) : Cube (OtherIndex I i) → ℝ :=
  fun y => q (extendOther i s y) / ((2 : ℝ) * coordinateMass q i s)

def coordinateDelta {I : Type*} [Fintype I] [DecidableEq I]
    (q : Cube I → ℝ) (i : I) : ℝ :=
  dirichletResource (centered q) -
    ∑ s : Bool, coordinateMass q i s *
      dirichletResource (centered (coordinatePosterior q i s))

def realSign (z : ℝ) : ℝ := if 0 ≤ z then 1 else -1

def oddMajority {n : ℕ} (x : Cube (Fin n)) : ℝ :=
  realSign (∑ i : Fin n, spin (x i))

def centralBinomialRatio (m : ℕ) : ℝ :=
  ((Nat.choose (2 * m) m : ℕ) : ℝ) / (2 : ℝ) ^ (2 * m)

/-- Claim 60229: the odd-majority tilt obstruction for the Fourier Dirichlet resource. -/
def majorityTiltDirichletObstruction : Prop :=
  ∀ (m : ℕ), 1 ≤ m →
    let n : ℕ := 2 * m + 1
    ∀ (a : ℝ), 0 < a → a ≤ (1 : ℝ) / 2 →
      let q : Cube (Fin n) → ℝ := fun x => 1 + a * oddMajority x
      let g : Cube (Fin n) → ℝ := centered q
      let b : ℝ := centralBinomialRatio m
      IsUniformDensity q ∧
      HasRevealTree q n ∧
      dirichletResource g = a ^ 2 * (n : ℝ) * b ∧
      dirichletResource g ≤ (n : ℝ) ∧
      uniformVariance g = a ^ 2 ∧
      (∀ i : Fin n,
        (∀ s : Bool, 0 < coordinateMass q i s) ∧
        coordinateDelta q i =
          a ^ 2 * b * (1 - (n : ℝ) * a ^ 2 * b ^ 2) /
            (1 - a ^ 2 * b ^ 2) ∧
        0 < coordinateDelta q i / uniformVariance g ∧
        coordinateDelta q i / uniformVariance g ≤ b) ∧
      b ≤ 1 / Real.sqrt ((m : ℝ) + 1) ∧
      ¬ ∃ c : ℝ,
        0 < c ∧
        ∀ (k n' : ℕ) (q' : Cube (Fin n') → ℝ),
          0 < n' →
          IsUniformDensity q' →
          HasRevealTree q' k →
          ∃ i : Fin n',
            coordinateDelta q' i ≥ c * uniformVariance (centered q')

/-- The coordinates not fixed by a reveal transcript. -/
abbrev Unrevealed (I : Type*) (D : Finset I) := {i : I // i ∉ D}

def agreesOn {I : Type*} [DecidableEq I]
    (D : Finset I) (h x : Cube I) : Prop :=
  ∀ i ∈ D, x i = h i

def transcriptMass {I : Type*} [Fintype I] [DecidableEq I]
    (q : Cube I → ℝ) (D : Finset I) (h : Cube I) : ℝ := by
  classical
  exact uniformExpectation (fun x => if agreesOn D h x then q x else 0)

def extendTranscript {I : Type*} [DecidableEq I]
    (D : Finset I) (h : Cube I) (y : Cube (Unrevealed I D)) : Cube I :=
  fun i => if hi : i ∈ D then h i else y ⟨i, hi⟩

def transcriptPosterior {I : Type*} [Fintype I] [DecidableEq I]
    (q : Cube I → ℝ) (D : Finset I) (h : Cube I) :
    Cube (Unrevealed I D) → ℝ :=
  fun y =>
    q (extendTranscript D h y) /
      ((2 : ℝ) ^ D.card * transcriptMass q D h)

def familyUnion {I J : Type*} [Fintype J] [DecidableEq I] [DecidableEq J]
    (S : J → Finset I) : Finset I :=
  Finset.biUnion Finset.univ S

def familyAmplitudeProduct {J : Type*} [Fintype J]
    (a : J → ℝ) : ℝ :=
  ∏ j : J, (1 + (a j) ^ 2)

def familyProductDensity {I J : Type*} [Fintype J] [DecidableEq I]
    (S : J → Finset I) (a : J → ℝ) (x : Cube I) : ℝ :=
  ∏ j : J, (1 + a j * parity (S j) x)

def activeFamilyIndices {I J : Type*} [Fintype J] [DecidableEq I]
    [DecidableEq J] (S : J → Finset I) (D : Finset I) : Finset J :=
  Finset.univ.filter (fun j => (S j \ D).Nonempty)

abbrev ActiveIndex {I J : Type*} [Fintype J] [DecidableEq I]
    [DecidableEq J] (S : J → Finset I) (D : Finset I) :=
  {j : J // j ∈ activeFamilyIndices S D}

def activeResidualSize {I J : Type*} [Fintype J] [DecidableEq I]
    [DecidableEq J] (S : J → Finset I) (D : Finset I) : ℝ :=
  ∑ j ∈ activeFamilyIndices S D, ((S j \ D).card : ℝ)

def residualParity {I : Type*} [Fintype I] [DecidableEq I]
    (D S : Finset I) (y : Cube (Unrevealed I D)) : ℝ :=
  ∏ i : {j : I // j ∈ S ∧ j ∉ D}, spin (y ⟨i.1, i.2.2⟩)

def HasResidualParityFactorization
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (S : J → Finset I) (D : Finset I)
    (q : Cube (Unrevealed I D) → ℝ) : Prop :=
  (∀ j : ActiveIndex S D, (S j.1 \ D).Nonempty) ∧
  (∀ j l : ActiveIndex S D, j ≠ l →
    Disjoint (S j.1 \ D) (S l.1 \ D)) ∧
  ∃ b : ActiveIndex S D → ℝ,
    (∀ j, -1 ≤ b j ∧ b j ≤ 1) ∧
    (∏ j : ActiveIndex S D, (1 + (b j) ^ 2) ≤ 2) ∧
    (∀ y, q y =
      ∏ j : ActiveIndex S D,
        (1 + b j * residualParity D (S j.1) y))

def activeAmplitudeProduct
    {I J : Type*} [Fintype J] [DecidableEq I] [DecidableEq J]
    (S : J → Finset I) (a : J → ℝ) (D : Finset I) : ℝ :=
  ∏ j : ActiveIndex S D, (1 + (a j.1) ^ 2)

def initialResidualResource
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (q : Cube I → ℝ) (S : J → Finset I) : ℝ :=
  (∑ j : J, ((S j).card : ℝ)) * uniformL2Squared (centered q)

def transcriptResource
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (q : Cube I → ℝ) (S : J → Finset I)
    (D : Finset I) (h : Cube I) : ℝ :=
  activeResidualSize S D *
    uniformL2Squared (centered (transcriptPosterior q D h))

/-- Claim 60230: the disjoint parity-product family with a pathwise resource payment. -/
def disjointProductParityResidualResource : Prop :=
  ∀ {I J : Type*} [Fintype I] [Fintype J]
      [DecidableEq I] [DecidableEq J]
      (S : J → Finset I) (a : J → ℝ),
    (∀ j, (S j).Nonempty) →
    (∀ j l, j ≠ l → Disjoint (S j) (S l)) →
    (∀ j, -1 ≤ a j ∧ a j ≤ 1) →
    familyAmplitudeProduct a ≤ 2 →
    let q : Cube I → ℝ := familyProductDensity S a
    let K : Finset I := familyUnion S
    let k : ℕ := K.card
    IsUniformDensity q ∧
    HasRevealTree q k ∧
    initialResidualResource q S ≤ (k : ℝ) ∧
    (∀ (D : Finset I) (h : Cube I),
      0 < transcriptMass q D h →
      IsUniformDensity (transcriptPosterior q D h) ∧
      HasResidualParityFactorization S D (transcriptPosterior q D h) ∧
      activeAmplitudeProduct S a D ≤ 2 ∧
      (activeResidualSize S D = 0 → transcriptResource q S D h = 0) ∧
      uniformVariance (centered (transcriptPosterior q D h)) =
        uniformL2Squared (centered (transcriptPosterior q D h))) ∧
    (∀ (D : Finset I) (h : Cube I),
      0 < transcriptMass q D h →
      0 < activeResidualSize S D →
      ∀ i : I, i ∈ K → i ∉ D →
      ∀ s : Bool,
        0 < transcriptMass q (insert i D) (Function.update h i s) →
        transcriptResource q S D h -
            transcriptResource q S (insert i D) (Function.update h i s) ≥
          uniformVariance (centered (transcriptPosterior q D h)))

end MathlibPlus.Open.ResidualNormBatch
