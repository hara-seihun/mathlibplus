import Mathlib

namespace MathlibPlus.Open.ResearchFormalize

abbrev C3Squared := (ZMod 3) × (ZMod 3)

def displacementLine (v : C3Squared) : AddSubgroup C3Squared :=
  AddSubgroup.closure ({v} : Set C3Squared)

def line10 : AddSubgroup C3Squared :=
  displacementLine ((1 : ZMod 3), (0 : ZMod 3))

def line01 : AddSubgroup C3Squared :=
  displacementLine ((0 : ZMod 3), (1 : ZMod 3))

def line11 : AddSubgroup C3Squared :=
  displacementLine ((1 : ZMod 3), (1 : ZMod 3))

def line12 : AddSubgroup C3Squared :=
  displacementLine ((1 : ZMod 3), (2 : ZMod 3))

def indexedDisplacementSubgroup : Fin 6 → AddSubgroup C3Squared
  | ⟨0, _⟩ => ⊥
  | ⟨1, _⟩ => line10
  | ⟨2, _⟩ => line01
  | ⟨3, _⟩ => line11
  | ⟨4, _⟩ => line12
  | ⟨5, _⟩ => ⊤

def isLineIndex (i : Fin 6) : Prop :=
  i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4

def pairGeneratesFull (i j : Fin 6) : Prop :=
  indexedDisplacementSubgroup i ⊔ indexedDisplacementSubgroup j = ⊤

def claim_31016 : Prop :=
  Function.Bijective indexedDisplacementSubgroup ∧
    ∀ i j : Fin 6,
      pairGeneratesFull i j ↔
        i = 5 ∨ j = 5 ∨ (isLineIndex i ∧ isLineIndex j ∧ i ≠ j)

abbrev DisplacementProfile := Fin 4 → Fin 6

def pairwiseSpanning (p : DisplacementProfile) : Prop :=
  ∀ i j : Fin 4, i ≠ j → pairGeneratesFull (p i) (p j)

noncomputable def fullRowCount (p : DisplacementProfile) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i : Fin 4 => p i = (5 : Fin 6))).card

noncomputable def lineRowCount (p : DisplacementProfile) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i : Fin 4 => isLineIndex (p i))).card

def fourFullRows (p : DisplacementProfile) : Prop :=
  fullRowCount p = 4

def threeFullRowsOneZeroOrLine (p : DisplacementProfile) : Prop :=
  fullRowCount p = 3 ∧ lineRowCount p ≤ 1

def twoFullRowsTwoDistinctLines (p : DisplacementProfile) : Prop :=
  fullRowCount p = 2 ∧ lineRowCount p = 2 ∧
    ∀ i j : Fin 4,
      i ≠ j → isLineIndex (p i) → isLineIndex (p j) → p i ≠ p j

def oneFullRowThreeDistinctLines (p : DisplacementProfile) : Prop :=
  fullRowCount p = 1 ∧ lineRowCount p = 3 ∧
    ∀ i j : Fin 4,
      i ≠ j → isLineIndex (p i) → isLineIndex (p j) → p i ≠ p j

def noFullRowFourDistinctLines (p : DisplacementProfile) : Prop :=
  fullRowCount p = 0 ∧ lineRowCount p = 4 ∧
    ∀ i j : Fin 4,
      i ≠ j → isLineIndex (p i) → isLineIndex (p j) → p i ≠ p j

noncomputable def pairwiseSpanningProfiles : Finset DisplacementProfile := by
  classical
  exact Finset.univ.filter pairwiseSpanning

noncomputable def fourFullProfiles : Finset DisplacementProfile := by
  classical
  exact Finset.univ.filter fourFullRows

noncomputable def threeFullProfiles : Finset DisplacementProfile := by
  classical
  exact Finset.univ.filter threeFullRowsOneZeroOrLine

noncomputable def twoFullProfiles : Finset DisplacementProfile := by
  classical
  exact Finset.univ.filter twoFullRowsTwoDistinctLines

noncomputable def oneFullProfiles : Finset DisplacementProfile := by
  classical
  exact Finset.univ.filter oneFullRowThreeDistinctLines

noncomputable def noFullProfiles : Finset DisplacementProfile := by
  classical
  exact Finset.univ.filter noFullRowFourDistinctLines

def claim_31017 : Prop :=
  (∀ p : DisplacementProfile,
    pairwiseSpanning p ↔
      fourFullRows p ∨
      threeFullRowsOneZeroOrLine p ∨
      twoFullRowsTwoDistinctLines p ∨
      oneFullRowThreeDistinctLines p ∨
      noFullRowFourDistinctLines p) ∧
    fourFullProfiles.card = 1 ∧
    threeFullProfiles.card = 20 ∧
    twoFullProfiles.card = 72 ∧
    oneFullProfiles.card = 96 ∧
    noFullProfiles.card = 24 ∧
    pairwiseSpanningProfiles.card = 213 ∧
    Fintype.card DisplacementProfile = 1296 ∧
    (6 : ℕ) ^ 4 = 1296

end MathlibPlus.Open.ResearchFormalize
