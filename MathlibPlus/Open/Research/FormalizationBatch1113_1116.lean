import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

abbrev Ternary := ZMod 3
abbrev TernaryCube (n : ℕ) := Fin n → Ternary
abbrev Cube3 := TernaryCube 3
abbrev ScalarFunction := Cube3 → Ternary

def odd (f : ScalarFunction) : Prop := ∀ x, f (-x) = -f x

def standardBasis (i : Fin 3) : Cube3 := Pi.single i 1

def normalizedOdd : Submodule Ternary ScalarFunction where
  carrier := {f | odd f ∧ ∀ i, f (standardBasis i) = 0}
  zero_mem' := by
    constructor
    · intro x
      simp [odd]
    · intro i
      simp [standardBasis]
  add_mem' := by
    intro f g hf hg
    constructor
    · intro x
      simp only [Pi.add_apply]
      rw [hf.1, hg.1]
      simp [add_comm]
    · intro i
      simp [hf.2 i, hg.2 i]
  smul_mem' := by
    intro r f hf
    constructor
    · intro x
      simp only [Pi.smul_apply]
      rw [hf.1]
      simp [smul_eq_mul]
    · intro i
      simp [hf.2 i]

/-- Representatives of the thirteen points of `PG(2,3)`, using the first
nonzero coordinate equal to one. -/
def projectiveDirectionReps : Fin 13 → Cube3 :=
  ![![1, 0, 0], ![1, 0, 1], ![1, 0, 2],
    ![1, 1, 0], ![1, 1, 1], ![1, 1, 2],
    ![1, 2, 0], ![1, 2, 1], ![1, 2, 2],
    ![0, 1, 0], ![0, 1, 1], ![0, 1, 2], ![0, 0, 1]]

/-- The ten non-coordinate projective points indexing normalized odd maps. -/
def nonCoordinateReps : Fin 10 → Cube3 :=
  ![![1, 0, 1], ![1, 0, 2],
    ![1, 1, 0], ![1, 1, 1], ![1, 1, 2],
    ![1, 2, 0], ![1, 2, 1], ![1, 2, 2],
    ![0, 1, 1], ![0, 1, 2]]

def normalizedEvaluation : normalizedOdd → (Fin 10 → Ternary) :=
  fun f i => f.1 (nonCoordinateReps i)

def scalarNormalizationFact : Prop :=
  ∀ f : ScalarFunction, odd f →
    ∃ ell : Cube3 →ₗ[Ternary] Ternary,
      (∀ x, (fun y => f y - ell y) (-x) = -(fun y => f y - ell y) x) ∧
      (∀ i, f (standardBasis i) - ell (standardBasis i) = 0)

noncomputable instance normalizedOddFintype : Fintype normalizedOdd := Fintype.ofFinite _

def normalizedOddScalarShadow : Prop :=
  scalarNormalizationFact ∧
  Module.finrank Ternary normalizedOdd = 10 ∧
  Function.Bijective normalizedEvaluation ∧
  Fintype.card normalizedOdd = 3 ^ 10

def secondDifferenceForm (x a c : Cube3) : ScalarFunction →ₗ[Ternary] Ternary where
  toFun f := (f (x + c + a) - f (x + c)) - (f (c + a) - f c)
  map_add' f g := by
    simp only [Pi.add_apply]
    ring
  map_smul' r f := by
    simp only [Pi.smul_apply, RingHom.id_apply]
    ring

def firstRelativeDerivativeForm (x a : Cube3) : ScalarFunction →ₗ[Ternary] Ternary where
  toFun f := f (a + x) - f a - f x
  map_add' f g := by
    simp only [Pi.add_apply]
    ring
  map_smul' r f := by
    simp only [Pi.smul_apply, RingHom.id_apply]
    ring

def secondDifferenceKernel (x : Cube3) : Submodule Ternary ScalarFunction where
  carrier := {f | ∀ a c, secondDifferenceForm x a c f = 0}
  zero_mem' := by
    intro a c
    simp
  add_mem' := by
    intro f g hf hg a c
    rw [map_add, hf a c, hg a c]
    simp
  smul_mem' := by
    intro r f hf a c
    rw [map_smul, hf a c]
    simp

def firstRelativeDerivativeKernel (x : Cube3) : Submodule Ternary ScalarFunction where
  carrier := {f | ∀ a, firstRelativeDerivativeForm x a f = 0}
  zero_mem' := by
    intro a
    simp
  add_mem' := by
    intro f g hf hg a
    rw [map_add, hf a, hg a]
    simp
  smul_mem' := by
    intro r f hf a
    rw [map_smul, hf a]
    simp

def shadowPlane (i : Fin 13) : Submodule Ternary ScalarFunction :=
  normalizedOdd ⊓ secondDifferenceKernel (projectiveDirectionReps i)

def firstShadowPlane (i : Fin 13) : Submodule Ternary ScalarFunction :=
  normalizedOdd ⊓ firstRelativeDerivativeKernel (projectiveDirectionReps i)

def oneDimensionalSubspace (K : Submodule Ternary ScalarFunction) :=
  {L : Submodule Ternary ScalarFunction // Module.finrank Ternary L = 1 ∧ L ≤ K}

noncomputable instance oneDimensionalSubspaceFinite
    (K : Submodule Ternary ScalarFunction) : Finite (oneDimensionalSubspace K) :=
  Finite.of_injective (fun L => L.1) Subtype.val_injective

noncomputable instance oneDimensionalSubspaceFintype
    (K : Submodule Ternary ScalarFunction) : Fintype (oneDimensionalSubspace K) :=
  Fintype.ofFinite _

def markedLine := Σ i : Fin 13, oneDimensionalSubspace (shadowPlane i)

def markedLineUnderlying : markedLine → Submodule Ternary ScalarFunction :=
  fun p => p.2.1

def shadowKernelDimensions : Prop :=
  ∀ i : Fin 13, Module.finrank Ternary (shadowPlane i) = 2

def markedLineCensus : Prop :=
  (∀ i : Fin 13, Fintype.card (oneDimensionalSubspace (shadowPlane i)) = 4) ∧
  Function.Injective markedLineUnderlying

def firstAndSecondShadowGeometry : Prop :=
  (∀ i : Fin 13, firstShadowPlane i = shadowPlane i) ∧ markedLineCensus

def claim_29033 : Prop := normalizedOddScalarShadow ∧ shadowKernelDimensions

def claim_29034 : Prop := shadowKernelDimensions ∧ firstAndSecondShadowGeometry

def claim_29054 : Prop :=
  normalizedOddScalarShadow ∧ shadowKernelDimensions ∧ firstAndSecondShadowGeometry

abbrev Q8 := QuaternionGroup 2
abbrev Cyclic3 := Multiplicative Ternary
abbrev C3SquaredQ8 := (Cyclic3 × Cyclic3) × Q8

def inverseAtoms (G : Type) [Group G] [DecidableEq G] :=
  {A : Finset G //
    A.Nonempty ∧
    (1 : G) ∉ A ∧
    (∀ g ∈ A, g⁻¹ ∈ A) ∧
    (∀ g ∈ A, A = {g, g⁻¹})}

def automorphismImage {G : Type} [Group G] [DecidableEq G] (α : MulAut G) (A : Finset G) : Finset G :=
  A.map α.toEquiv.toEmbedding

def inverseAtomActionFaithful (G : Type) [Group G] [DecidableEq G] : Prop :=
  (∀ α : MulAut G, ∀ A : inverseAtoms G,
    ∃ B : inverseAtoms G, automorphismImage α A.1 = B.1) ∧
  (∀ α β : MulAut G,
    (∀ A : inverseAtoms G,
      automorphismImage α A.1 = automorphismImage β A.1) → α = β)

def claim_29040 : Prop :=
  Nonempty (MulAut C3SquaredQ8 ≃* 
    (Matrix.GeneralLinearGroup (Fin 2) Ternary × MulAut Q8)) ∧
  Nat.card (MulAut C3SquaredQ8) = 48 * 24 ∧
  48 * 24 = 1152 ∧
  inverseAtomActionFaithful C3SquaredQ8

def connectionSets (G : Type) [Group G] [Fintype G] [DecidableEq G] :=
  {S : Finset G //
    (1 : G) ∉ S ∧ ∀ g, g ∈ S ↔ g⁻¹ ∈ S}

noncomputable instance connectionSetsFinite
    (G : Type) [Group G] [Fintype G] [DecidableEq G] :
    Finite (connectionSets G) :=
  Finite.of_injective (fun S => S.1) Subtype.val_injective

noncomputable instance connectionSetsFintype
    (G : Type) [Group G] [Fintype G] [DecidableEq G] :
    Fintype (connectionSets G) := Fintype.ofFinite _

def automorphismImageConnection
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (α : MulAut G) (S : connectionSets G) : connectionSets G := by
  refine ⟨automorphismImage α S.1, ?_, ?_⟩
  · intro h
    rcases Finset.mem_map.1 h with ⟨g, hg, hα⟩
    apply S.2.1
    have : g = 1 := α.injective (by simpa using hα)
    simpa [this] using hg
  · intro g
    constructor
    · intro hg
      rcases Finset.mem_map.1 hg with ⟨h, hh, rfl⟩
      apply Finset.mem_map.2
      refine ⟨h⁻¹, (S.2.2 h).mp hh, ?_⟩
      simp
    · intro hg
      rcases Finset.mem_map.1 hg with ⟨h, hh, hmap⟩
      apply Finset.mem_map.2
      refine ⟨h⁻¹, (S.2.2 h).mp hh, ?_⟩
      change α (h⁻¹) = g
      change α h = g⁻¹ at hmap
      calc
        α (h⁻¹) = (α h)⁻¹ := by simp
        _ = (g⁻¹)⁻¹ := by rw [hmap]
        _ = g := by simp

noncomputable instance connectionSetsMulAction
    (G : Type) [Group G] [Fintype G] [DecidableEq G] :
    MulAction (MulAut G) (connectionSets G) where
  smul α S := automorphismImageConnection G α S
  one_smul S := by
    apply Subtype.ext
    change S.1.map (1 : MulAut G).toEquiv.toEmbedding = S.1
    rw [show (1 : MulAut G).toEquiv.toEmbedding = Function.Embedding.refl G by
      ext g
      simp]
    exact Finset.map_refl
  mul_smul α β S := by
    apply Subtype.ext
    change S.1.map (α * β).toEquiv.toEmbedding =
      (S.1.map β.toEquiv.toEmbedding).map α.toEquiv.toEmbedding
    rw [Finset.map_map]
    congr 1

noncomputable instance connectionOrbitQuotientFintype :
    Fintype (Quotient (MulAction.orbitRel (MulAut C3SquaredQ8)
      (connectionSets C3SquaredQ8))) := Fintype.ofFinite _

def cayleyGraph {G : Type} [Group G] [Fintype G] [DecidableEq G]
    (S : connectionSets G) : SimpleGraph G where
  Adj x y := x ≠ y ∧ x⁻¹ * y ∈ S.1
  symm := ⟨fun x y h =>
    ⟨h.1.symm, by simpa using (S.2.2 (x⁻¹ * y)).mp h.2⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

def claim_29045 : Prop :=
  ∀ S T : connectionSets C3SquaredQ8,
    Nonempty (SimpleGraph.Iso (cayleyGraph S) (cayleyGraph T)) →
      ∃ α : MulAut C3SquaredQ8,
        automorphismImageConnection C3SquaredQ8 α S = T

def claim_29042 : Prop :=
  Nat.card (MulAut C3SquaredQ8) = 1152 ∧
  inverseAtomActionFaithful C3SquaredQ8 ∧
  Fintype.card (connectionSets C3SquaredQ8) = 2 ^ 36 ∧
  Fintype.card
      (Quotient (MulAction.orbitRel (MulAut C3SquaredQ8)
        (connectionSets C3SquaredQ8))) = 74041240

abbrev PartialInversionGroup (m : ℕ) :=
  (Cyclic3 × Cyclic3) × DihedralGroup m

abbrev PartialInversionTriples (m : ℕ) :=
  (Cyclic3 × Cyclic3) × (ZMod m × Bool)

def dihedralCoordinateEquiv (m : ℕ) :
    DihedralGroup m ≃ (ZMod m × Bool) where
  toFun g := match g with
    | DihedralGroup.r z => (z, false)
    | DihedralGroup.sr z => (z, true)
  invFun p := match p.2 with
    | false => DihedralGroup.r p.1
    | true => DihedralGroup.sr p.1
  left_inv g := by cases g <;> rfl
  right_inv p := by
    cases p with
    | mk z e => cases e <;> rfl

def partialInversionCoordinateEquiv (m : ℕ) :
    PartialInversionGroup m ≃ PartialInversionTriples m :=
  Equiv.prodCongr (Equiv.refl (Cyclic3 × Cyclic3)) (dihedralCoordinateEquiv m)

def partialInversionRotation (m : ℕ) : PartialInversionGroup m :=
  ((1, 1), DihedralGroup.r 1)

def partialInversionReflection (m : ℕ) : PartialInversionGroup m :=
  ((1, 1), DihedralGroup.sr 0)

def partialInversionHypothesis (m : ℕ) : Prop :=
  Odd m ∧ 1 < m ∧ Nat.Coprime m 3

def claim_29069 : Prop :=
  ∀ m : ℕ, partialInversionHypothesis m →
    Nonempty (PartialInversionGroup m ≃ PartialInversionTriples m) ∧
    (∀ a : Cyclic3 × Cyclic3,
      partialInversionReflection m * (a, 1) =
        (a, 1) * partialInversionReflection m) ∧
    partialInversionReflection m * partialInversionRotation m *
        (partialInversionReflection m)⁻¹ =
      (partialInversionRotation m)⁻¹

def claim_29073 : Prop :=
  ∀ m : ℕ, partialInversionHypothesis m →
    ∀ a : Cyclic3 × Cyclic3, ∀ z : ZMod m,
      ((a, DihedralGroup.r z) : PartialInversionGroup m)⁻¹ =
        (a⁻¹, DihedralGroup.r (-z)) ∧
      ((a, DihedralGroup.sr z) : PartialInversionGroup m)⁻¹ =
        (a⁻¹, DihedralGroup.sr z)

end MathlibPlus.Open.ResearchFormalizationBatch
