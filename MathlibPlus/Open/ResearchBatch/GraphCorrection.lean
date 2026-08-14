import Mathlib

namespace MathlibPlus.Open.ResearchBatch

abbrev GraphW := Fin 3 → ZMod 3
abbrev GraphV := Fin 5 → ZMod 3
abbrev GraphScalar := ZMod 3

noncomputable def graphCorrection (x : GraphW) : GraphV :=
  ![x 0 * (x 1)^2,
    x 0 * (x 2)^2,
    (x 1)^2 * x 2,
    x 1 * (x 2)^2,
    x 0 * x 1 * x 2]

noncomputable def graphPsi (p : GraphW × GraphV) : GraphW × GraphV :=
  (p.1, p.2 + graphCorrection p.1)

def graphFirst : (GraphW × GraphV) →ₗ[GraphScalar] GraphW :=
  { toFun := Prod.fst
    map_add' := by intro x y; rfl
    map_smul' := by intro a x; rfl }

def graphFiberEmbedding : GraphV →ₗ[GraphScalar] (GraphW × GraphV) :=
  { toFun := fun v => (0, v)
    map_add' := by intro x y; rfl
    map_smul' := by intro a x; rfl }

def graphProjection (U : Submodule GraphScalar (GraphW × GraphV)) :
    Submodule GraphScalar GraphW :=
  Submodule.map graphFirst U

def graphKernel (U : Submodule GraphScalar (GraphW × GraphV)) :
    Submodule GraphScalar GraphV :=
  U.comap graphFiberEmbedding

def graphLinearSubspace (S : Set (GraphW × GraphV)) : Prop :=
  ∃ U : Submodule GraphScalar (GraphW × GraphV), (U : Set (GraphW × GraphV)) = S

def graphCorrectionAdditiveModulo
    (P : Submodule GraphScalar GraphW) (K : Submodule GraphScalar GraphV) : Prop :=
  ∀ x y : GraphW, x ∈ P → y ∈ P →
    graphCorrection (x + y) - graphCorrection x - graphCorrection y ∈ K

def subspaceGraphCorrectionCriterion : Prop :=
  ∀ U : Submodule GraphScalar (GraphW × GraphV),
    graphLinearSubspace (graphPsi '' (U : Set (GraphW × GraphV))) ↔
      graphCorrectionAdditiveModulo (graphProjection U) (graphKernel U)

def noRankSevenGraphExtraction : Prop :=
  (∀ U : Submodule GraphScalar (GraphW × GraphV),
    Module.finrank GraphScalar U = 7 →
    Module.finrank GraphScalar (graphProjection U) = 3 →
    Module.finrank GraphScalar (graphKernel U) = 4 →
      ¬ graphLinearSubspace (graphPsi '' (U : Set (GraphW × GraphV)))) ∧
  (∀ K : Submodule GraphScalar GraphV,
    Module.finrank GraphScalar K = 4 →
      ¬ graphCorrectionAdditiveModulo (⊤ : Submodule GraphScalar GraphW) K)

abbrev graphPlane := {P : Submodule GraphScalar GraphW // Module.finrank GraphScalar P = 2}
abbrev graphHyperplane := {K : Submodule GraphScalar GraphV // Module.finrank GraphScalar K = 4}

abbrev graphCompatiblePair :=
  {pk : graphPlane × graphHyperplane //
    graphCorrectionAdditiveModulo pk.1.1 pk.2.1}

abbrev graphLinearLift (pk : graphCompatiblePair) :=
  pk.1.1 →ₗ[GraphScalar] GraphV ⧸ pk.1.2.1

noncomputable instance : Fintype graphCompatiblePair := Fintype.ofFinite _
noncomputable def graphCandidateSubspace
    (pk : graphCompatiblePair) (ell : graphLinearLift pk) :
    Submodule GraphScalar (GraphW × GraphV) :=
  { carrier := {p | ∃ hp : p.1 ∈ pk.1.1.1,
        Submodule.mkQ pk.1.2.1 p.2 = ell ⟨p.1, hp⟩}
    zero_mem' := by
      refine ⟨pk.1.1.1.zero_mem, ?_⟩
      change Submodule.mkQ pk.1.2.1 0 = ell ⟨0, _⟩
      calc
        Submodule.mkQ pk.1.2.1 0 = 0 := map_zero _
        _ = ell (0 : pk.1.1.1) := (ell.map_zero).symm
        _ = ell ⟨0, _⟩ := by congr 1
    add_mem' := by
      rintro x y ⟨hx, hxeq⟩ ⟨hy, hyeq⟩
      refine ⟨pk.1.1.1.add_mem hx hy, ?_⟩
      change Submodule.mkQ pk.1.2.1 (x.2 + y.2) = ell ⟨x.1 + y.1, _⟩
      calc
        Submodule.mkQ pk.1.2.1 (x.2 + y.2) =
            Submodule.mkQ pk.1.2.1 x.2 + Submodule.mkQ pk.1.2.1 y.2 := map_add _ _ _
        _ = ell ⟨x.1, hx⟩ + ell ⟨y.1, hy⟩ := by rw [hxeq, hyeq]
        _ = ell (⟨x.1, hx⟩ + ⟨y.1, hy⟩) := (ell.map_add _ _).symm
        _ = ell ⟨x.1 + y.1, _⟩ := by congr 1
    smul_mem' := by
      intro a x ⟨hx, hxeq⟩
      refine ⟨pk.1.1.1.smul_mem a hx, ?_⟩
      change Submodule.mkQ pk.1.2.1 (a • x.2) = ell ⟨a • x.1, _⟩
      calc
        Submodule.mkQ pk.1.2.1 (a • x.2) =
            a • Submodule.mkQ pk.1.2.1 x.2 := map_smul _ _ _
        _ = a • ell ⟨x.1, hx⟩ := by rw [hxeq]
        _ = ell (a • (⟨x.1, hx⟩ : pk.1.1.1)) := (ell.map_smul _ _).symm
        _ = ell ⟨a • x.1, _⟩ := by congr 1 }

noncomputable def rankSixPlaneHyperplaneCensus : Prop :=
  Fintype.card graphPlane = 13 ∧
  Fintype.card graphHyperplane = 121 ∧
  Fintype.card graphCompatiblePair = 277 ∧
  (∀ pk : graphCompatiblePair, Nonempty (Fin 9 ≃ graphLinearLift pk)) ∧
  (∀ (pk : graphCompatiblePair) (ell : graphLinearLift pk),
    Module.finrank GraphScalar (graphCandidateSubspace pk ell) = 6) ∧
  Nonempty (Fin 2493 ≃ Σ pk : graphCompatiblePair, graphLinearLift pk)

end MathlibPlus.Open.ResearchBatch
