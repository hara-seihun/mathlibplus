import Mathlib

namespace MathlibPlus.Open.ResearchFormalizeBatch

noncomputable section

/-! The fully specified characteristic-seven row switch from Claim 58826. -/

abbrev F7 := ZMod 7
abbrev A7 := Fin 3 → F7
abbrev B7 := Fin 4 → F7
abbrev G7 := A7 × B7

def covector : Fin 7 → A7 :=
  ![![6, 6, 2], ![3, 4, 3], ![6, 4, 3], ![5, 0, 2],
    ![3, 4, 3], ![4, 0, 4], ![1, 4, 3]]

def direction : Fin 7 → B7 :=
  ![![1, 6, 6, 5], ![1, 2, 3, 1], ![0, 1, 1, 6], ![1, 5, 1, 5],
    ![1, 2, 0, 1], ![1, 3, 5, 5], ![0, 0, 1, 2]]

def dot7 (u : A7) (a : A7) : F7 :=
  ∑ j : Fin 3, u j * a j

def row (i : Fin 7) (c : F7) : Set G7 :=
  {z | z.2 = direction i ∧ dot7 (covector i) z.1 = c}

def negateSet (S : Set G7) : Set G7 :=
  {z | -z ∈ S}

def switchRows (c : Fin 7 → F7) : Set G7 :=
  ⋃ i : Fin 7, row i (c i) ∪ negateSet (row i (c i))

def shearMatrix : Fin 3 → Fin 4 → F7 :=
  ![![1, 5, 6, 2], ![0, 0, 3, 6], ![0, 0, 0, 0]]

def independentShearMatrix : Fin 3 → Fin 4 → F7 :=
  ![![6, 6, 3, 2], ![6, 0, 0, 0], ![0, 0, 0, 0]]

def shear (M : Fin 3 → Fin 4 → F7) (x : B7) : A7 :=
  fun i => ∑ j : Fin 4, M i j * x j

def lambda : Fin 7 → F7 :=
  ![1, 6, 0, 0, 0, 0, 0]

def theta (M : Fin 3 → Fin 4 → F7) : G7 → G7 :=
  fun z => (z.1 + shear M z.2, z.2)

def characteristicSevenLinearGraphification : Prop :=
  (∀ (i : Fin 7) (x : B7),
    dot7 (covector i) (shear shearMatrix (x + direction i) - shear shearMatrix x) =
      lambda i) ∧
  (∀ (x : B7), shear shearMatrix (-x) = -shear shearMatrix x) ∧
  Function.Bijective (theta shearMatrix) ∧
  (∀ (z w : G7), theta shearMatrix (z + w) = theta shearMatrix z + theta shearMatrix w) ∧
  (∀ (a : F7) (z : G7), theta shearMatrix (a • z) = a • theta shearMatrix z) ∧
  Set.image (theta shearMatrix) (switchRows (fun _ => 0)) =
    switchRows lambda ∧
  (∀ (i : Fin 7),
    Set.image (theta shearMatrix) (negateSet (row i 0)) =
      negateSet (row i (lambda i))) ∧
  (∀ (i : Fin 7) (x : B7),
    dot7 (covector i)
      (shear independentShearMatrix (x + direction i) -
        shear independentShearMatrix x) = lambda i)

/-! The labelled projective obstruction in Claim 58838. -/

abbrev V (p : ℕ) := Fin 3 → ZMod p

def pMode {p : ℕ} : Fin 3 → V p :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]

def qMode {p : ℕ} (t : Fin 2) : Fin 3 → V p :=
  ![![1, 0, 0], ![1, 1, 1], ![1, 2, (t : ZMod p)]]

def projectiveLine {p : ℕ} [Fact p.Prime] (v : V p) : Submodule (ZMod p) (V p) :=
  Submodule.span (ZMod p) {v}

def preservesLabelledModes {p : ℕ} [Fact p.Prime]
    (A : V p ≃ₗ[ZMod p] V p) : Prop :=
  (∀ k : Fin 3,
    Submodule.map A.toLinearMap (projectiveLine (pMode (p := p) k)) =
      projectiveLine (pMode (p := p) k)) ∧
  (∀ k : Fin 3,
    Submodule.map A.toLinearMap (projectiveLine (qMode (p := p) 0 k)) =
      projectiveLine (qMode (p := p) 1 k))

def labelledGlobalScalarTransporterObstruction : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p), p % 3 = 1 →
    letI : Fact p.Prime := ⟨hp⟩
    ∀ A : V p ≃ₗ[ZMod p] V p, ¬ preservesLabelledModes A

/-! The explicit Fourier-mode code carrier and dimension/projection interface. -/

def fourierTuple {p : ℕ} (ζ : ZMod p)
    (u₀ u₁ u₂ : V p) : Fin 3 → V p :=
  ![u₀ + u₁ + u₂,
    u₀ + ζ • u₁ + (ζ ^ 2) • u₂,
    u₀ + (ζ ^ 2) • u₁ + ζ • u₂]

def fourierGeneratingSet {p : ℕ} [Fact p.Prime]
    (ζ : ZMod p) (U₀ U₁ U₂ : Submodule (ZMod p) (V p)) :
    Set (Fin 3 → V p) :=
  {y | ∃ u₀ u₁ u₂,
    u₀ ∈ U₀ ∧ u₁ ∈ U₁ ∧ u₂ ∈ U₂ ∧
      y = fourierTuple ζ u₀ u₁ u₂}

def fourierCode {p : ℕ} [Fact p.Prime]
    (ζ : ZMod p) (U₀ U₁ U₂ : Submodule (ZMod p) (V p)) :
    Submodule (ZMod p) (Fin 3 → V p) :=
  Submodule.span (ZMod p) (fourierGeneratingSet ζ U₀ U₁ U₂)

def coordinateProjection {p : ℕ} [Fact p.Prime]
    (K : Submodule (ZMod p) (Fin 3 → V p)) (i : Fin 3) :
    K → V p := fun y => y.1 i

def blockwiseRegular {p : ℕ} [Fact p.Prime]
    (K : Submodule (ZMod p) (Fin 3 → V p)) : Prop :=
  ∀ i : Fin 3, Function.Bijective (coordinateProjection K i)

def determinantOfThree {p : ℕ}
    (a b c : V p) : ZMod p :=
  Matrix.det (fun i j => ![a, b, c] i j)

def fourierCodeInterface : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p), p % 3 = 1 →
    letI : Fact p.Prime := ⟨hp⟩
    ∀ ζ : ZMod p, orderOf ζ = 3 →
      let P :=
        fourierCode ζ
          (projectiveLine (pMode (p := p) 0))
          (projectiveLine (pMode (p := p) 1))
          (projectiveLine (pMode (p := p) 2))
      let Q : Fin 2 → Submodule (ZMod p) (Fin 3 → V p) := fun t =>
        fourierCode ζ
          (projectiveLine (pMode (p := p) 0))
          (projectiveLine (![1, 1, 1] : V p))
          (projectiveLine (![1, 2, (t : ZMod p)] : V p))
      (∀ y, y ∈ P ↔ ∃ u₀ u₁ u₂,
        u₀ ∈ projectiveLine (pMode (p := p) 0) ∧
        u₁ ∈ projectiveLine (pMode (p := p) 1) ∧
        u₂ ∈ projectiveLine (pMode (p := p) 2) ∧
        y = fourierTuple ζ u₀ u₁ u₂) ∧
      (∀ t y, y ∈ Q t ↔ ∃ u₀ u₁ u₂,
        u₀ ∈ projectiveLine (pMode (p := p) 0) ∧
        u₁ ∈ projectiveLine (![1, 1, 1] : V p) ∧
        u₂ ∈ projectiveLine (![1, 2, (t : ZMod p)] : V p) ∧
        y = fourierTuple ζ u₀ u₁ u₂) ∧
      Module.finrank (ZMod p) P = 3 ∧
      (∀ t : Fin 2, Module.finrank (ZMod p) (Q t) = 3) ∧
      blockwiseRegular P ∧
      (∀ t : Fin 2, blockwiseRegular (Q t)) ∧
      7 ≤ p ∧
      (∀ t : Fin 2,
        determinantOfThree
          (pMode (p := p) 0)
          (![1, 1, 1] : V p)
          (![1, 2, (t : ZMod p)] : V p) =
            (t : ZMod p) - 2 ∧
        determinantOfThree
          (pMode (p := p) 0)
          (![1, 1, 1] : V p)
          (![1, 2, (t : ZMod p)] : V p) ≠ 0)

def joinedModeSubspace {p : ℕ} [Fact p.Prime] (t : Fin 2) :
    Fin 3 → Submodule (ZMod p) (V p) :=
  ![projectiveLine (pMode (p := p) 0) + projectiveLine (pMode (p := p) 0),
    projectiveLine (pMode (p := p) 1) +
      projectiveLine (![1, 1, 1] : V p),
    projectiveLine (pMode (p := p) 2) +
      projectiveLine (![1, 2, (t : ZMod p)] : V p)]

def pairProjection {p : ℕ} [Fact p.Prime]
    (K : Submodule (ZMod p) (Fin 3 → V p)) (i j : Fin 3) :
    K → V p × V p := fun y => (y.1 i, y.1 j)

def coordinateImage {p : ℕ} [Fact p.Prime]
    (K : Submodule (ZMod p) (Fin 3 → V p)) (i : Fin 3) :
    Submodule (ZMod p) (V p) :=
  Submodule.span (ZMod p) (Set.range (coordinateProjection K i))

def pairImage {p : ℕ} [Fact p.Prime]
    (K : Submodule (ZMod p) (Fin 3 → V p)) (i j : Fin 3) :
    Submodule (ZMod p) (V p × V p) :=
  Submodule.span (ZMod p) (Set.range (pairProjection K i j))

def pairwiseGoursatShadowCollision : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p), p % 3 = 1 →
    letI : Fact p.Prime := ⟨hp⟩
    ∀ ζ : ZMod p, orderOf ζ = 3 →
      let P :=
        fourierCode ζ
          (projectiveLine (pMode (p := p) 0))
          (projectiveLine (pMode (p := p) 1))
          (projectiveLine (pMode (p := p) 2))
      let Q : Fin 2 → Submodule (ZMod p) (Fin 3 → V p) := fun t =>
        fourierCode ζ
          (projectiveLine (pMode (p := p) 0))
          (projectiveLine (![1, 1, 1] : V p))
          (projectiveLine (![1, 2, (t : ZMod p)] : V p))
      (∀ t : Fin 2,
        Module.finrank (ZMod p) (joinedModeSubspace (p := p) t 0) = 1 ∧
        Module.finrank (ZMod p) (joinedModeSubspace (p := p) t 1) = 2 ∧
        Module.finrank (ZMod p) (joinedModeSubspace (p := p) t 2) = 2) ∧
      (∀ t : Fin 2,
        Module.finrank (ZMod p) (P + Q t) = 5) ∧
      (∀ t : Fin 2, ∀ i : Fin 3,
        Module.finrank (ZMod p) (coordinateImage (P + Q t) i) = 3) ∧
      (∀ t : Fin 2, ∀ i j : Fin 3, i ≠ j →
        Function.Injective (pairProjection (P + Q t) i j)) ∧
      (∀ t : Fin 2, ∀ i j : Fin 3, i ≠ j →
        Module.finrank (ZMod p) (pairImage (P + Q t) i j) = 5)

end
end MathlibPlus.Open.ResearchFormalizeBatch
