import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.FiniteField

abbrev F2 := ZMod 2
abbrev QuotientSpace := Fin 3 → F2
abbrev CoordinateSpace (n : ℕ) := Fin n → F2

/-- The three-bit representative of the integer label used in the packet. -/
def bitVector (m : ℕ) : QuotientSpace :=
  fun k => ((m / 2 ^ k.1) % 2 : ℕ)

noncomputable def aSet : Finset QuotientSpace :=
  {bitVector 0, bitVector 1, bitVector 2}

noncomputable def pSet : Finset QuotientSpace :=
  {bitVector 0, bitVector 1, bitVector 2, bitVector 3}

noncomputable def sSet : Finset QuotientSpace :=
  Finset.univ \ aSet

def otherRank {n : ℕ} (i j : Fin n) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun k => k < j ∧ k ≠ i)).card

/-- Columns 4, 5, 6 are assigned to the first three other coordinates,
    and column 4 is repeated thereafter. -/
noncomputable def quotientColumn (n : ℕ) (i j : Fin n) : QuotientSpace :=
  if i = j then 0 else
    match otherRank i j with
    | 0 => bitVector 4
    | 1 => bitVector 5
    | 2 => bitVector 6
    | _ => bitVector 4

noncomputable def affineQuotient (n : ℕ) (i : Fin n) (x : CoordinateSpace n) : QuotientSpace :=
  ∑ j : Fin n, if i = j then 0 else x j • quotientColumn n i j

noncomputable def coordinateFunction (n : ℕ) (i : Fin n)
    (x : CoordinateSpace n) : Bool :=
  if affineQuotient n i x ∈ sSet then true else false

def coordinateBasis (n : ℕ) (j : Fin n) : CoordinateSpace n :=
  fun k => if k = j then 1 else 0

noncomputable def translationOrbit (n : ℕ) (i : Fin n) :
    Finset (CoordinateSpace n → Bool) := by
  classical
  exact
    (Finset.univ : Finset (CoordinateSpace n)).image
      (fun t => fun x => coordinateFunction n i (x + t))

noncomputable def directionDensity (n : ℕ) (i : Fin n) : ℚ :=
  ((Finset.univ.filter (fun x : CoordinateSpace n =>
      coordinateFunction n i x = true)).card : ℚ) /
    (Fintype.card (CoordinateSpace n) : ℚ)

noncomputable def directionEnergy (n : ℕ) (i j : Fin n) : ℚ :=
  ((Finset.univ.filter (fun x : CoordinateSpace n =>
      coordinateFunction n i x = true ∧
      coordinateFunction n i (x + coordinateBasis n j) = true)).card : ℚ) /
    (Fintype.card (CoordinateSpace n) : ℚ)

def columnsSpan : Prop :=
  ∀ y : QuotientSpace, ∃ α β γ : F2,
    α • bitVector 4 + β • bitVector 5 + γ • bitVector 6 = y

def aHasTrivialTranslationStabilizer : Prop :=
  ∀ t : QuotientSpace,
    aSet.image (fun y => y + t) = aSet → t = 0

noncomputable def explicitOrbitEightAffineCoordinateTuple : Prop :=
  ∀ (n : ℕ), 4 ≤ n → ∀ i : Fin n,
    columnsSpan ∧
    aHasTrivialTranslationStabilizer ∧
    (translationOrbit n i).card = 8 ∧
    directionDensity n i = (5 : ℚ) / 8

def translatedSet (s : Finset QuotientSpace) (v : QuotientSpace) :
    Finset QuotientSpace :=
  s.image (fun y => y + v)

noncomputable def scalarOppositePairEnergy : Prop :=
  (∀ v : QuotientSpace, v ∉ pSet →
    sSet ∩ translatedSet sSet v = {bitVector 3, bitVector 3 + v}) ∧
  (∀ (n : ℕ), 4 ≤ n → ∀ i j : Fin n, i ≠ j →
    quotientColumn n i j ∉ pSet ∧
    directionEnergy n i j = (1 : ℚ) / 4 ∧
    directionEnergy n i j + directionEnergy n j i = (1 : ℚ) / 2 ∧
    directionEnergy n i j + directionEnergy n j i ≤ 1) ∧
  (∀ (n : ℕ), 4 ≤ n →
    (∑ i : Fin n, directionDensity n i) =
      ((5 : ℚ) * (n : ℚ)) / 8)

noncomputable def pairProjection (n : ℕ) (i j : Fin n) : Finset QuotientSpace :=
  (Finset.univ : Finset (CoordinateSpace n)).image (affineQuotient n i)

noncomputable def globalPairwiseAffineGluingContradiction : Prop :=
  ∀ (n : ℕ), 3 ≤ n → ∀ i j k : Fin n,
    i ≠ j → i ≠ k → j ≠ k →
      (∀ ℓ : Fin n, ℓ ≠ i →
        quotientColumn n i ℓ ∈ pairProjection n i j) ∧
      quotientColumn n i k ∉ pSet ∧
      (pairProjection n i j = pSet → False)

noncomputable def explicitCompleteCoordinateSquare : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n),
    let i₀ : Fin n := ⟨0, by omega⟩
    let i₁ : Fin n := ⟨1, by omega⟩
    let e₂ : Fin n := ⟨2, by omega⟩
    let e₃ : Fin n := ⟨3, by omega⟩
    let x := coordinateBasis n e₂ + coordinateBasis n e₃
    let e₀ := coordinateBasis n i₀
    let e₁ := coordinateBasis n i₁
    affineQuotient n i₀ x = bitVector 3 ∧
    affineQuotient n i₁ x = bitVector 3 ∧
    quotientColumn n i₀ i₁ = bitVector 4 ∧
    quotientColumn n i₁ i₀ = bitVector 4 ∧
    affineQuotient n i₀ (x + e₁) = bitVector 7 ∧
    affineQuotient n i₁ (x + e₀) = bitVector 7 ∧
    bitVector 3 ∈ sSet ∧
    bitVector 7 ∈ sSet

end MathlibPlus.Open.ResearchFormalization.FiniteField
