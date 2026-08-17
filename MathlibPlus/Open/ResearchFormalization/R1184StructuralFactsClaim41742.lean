import MathlibPlus.Open.ProjectsResearch.CayleyCIClaims
import MathlibPlus.Open.ResearchFormalization60980

open Classical

namespace MathlibPlus.Open.ResearchFormalization.R1184StructuralFactsClaim41742

noncomputable section

open MathlibPlus.Open
open MathlibPlus.Open.ResearchFormalization60980

/-- Powers for the displayed semidirect operation. -/
def ePow (m : ℕ) (g : eCarrier m 8) : ℕ → eCarrier m 8
  | 0 => eIdentity m 8
  | n + 1 => eMul m 8 (ePow m g n) g

/-- The group, identity, and inverse laws of the displayed carrier. -/
def eGroupAxioms (m : ℕ) : Prop :=
  (∀ x y z : eCarrier m 8,
    eMul m 8 (eMul m 8 x y) z = eMul m 8 x (eMul m 8 y z)) ∧
    (∀ x : eCarrier m 8,
      eMul m 8 (eIdentity m 8) x = x ∧
        eMul m 8 x (eIdentity m 8) = x) ∧
      (∀ x : eCarrier m 8,
        eMul m 8 (eInv m 8 x) x = eIdentity m 8 ∧
          eMul m 8 x (eInv m 8 x) = eIdentity m 8)

/-- The presentation generators and relations of `E(C_m,8)`. -/
def ePresentationRelations (m : ℕ) : Prop :=
  ePow m (1, 0) m = eIdentity m 8 ∧
    ePow m (0, 1) 8 = eIdentity m 8 ∧
      eMul m 8
          (eMul m 8 (eInv m 8 (0, 1)) (1, 0))
          (0, 1) = eInv m 8 (1, 0)

/-- The commutator-generated subgroup in the displayed carrier. -/
def eDerivedSet (m : ℕ) : Set (eCarrier m 8) :=
  eGenerated m
    (Set.range (fun p : eCarrier m 8 × eCarrier m 8 =>
      eMul m 8
        (eMul m 8 (eMul m 8 p.1 p.2) (eInv m 8 p.1))
        (eInv m 8 p.2)))

def eIsSubgroup (m : ℕ) (U : Set (eCarrier m 8)) : Prop :=
  eSubgroupClosed m U U

/-- The quotient map to the outer cyclic factor. -/
def eOuterProjection (m : ℕ) (x : eCarrier m 8) : ZMod 8 :=
  x.2

def eOuterProjectionHom (m : ℕ) : Prop :=
  (∀ x y : eCarrier m 8,
    eOuterProjection m (eMul m 8 x y) =
      eOuterProjection m x + eOuterProjection m y) ∧
    Function.Surjective (eOuterProjection m) ∧
      eOuterProjection m (eIdentity m 8) = 0 ∧
        (∀ x : eCarrier m 8,
          eOuterProjection m x = 0 ↔ x ∈ eDerivedSet m)

/-- The standard generators of the kernel and the outer cyclic factor. -/
def eA (m : ℕ) : eCarrier m 8 := (1, 0)
def eB (m : ℕ) : eCarrier m 8 := (0, 1)

/-- Claim 41742: structural facts for the actual displayed
`E(C_m,8)=C_m⋊C₈` carrier, including the derived/abelianized structure,
the cyclic Sylow-2 factor, and the characteristic unique odd Hall subgroup. -/
def claim41742 : Prop :=
  ∀ (m : ℕ),
    Odd m →
      eGroupAxioms m ∧
        ePresentationRelations m ∧
          Nat.card (eCarrier m 8) = 8 * m ∧
            eDerivedSet m = eRotationAxis m ∧
              eRotationAxis m = eGenerated m ({eA m} : Set (eCarrier m 8)) ∧
                Set.ncard (eRotationAxis m) = m ∧
                  eOuterProjectionHom m ∧
                    eIsSubgroup m (eOuterAxis m) ∧
                      Set.ncard (eOuterAxis m) = 8 ∧
                        (∀ x : eCarrier m 8,
                          x ∈ eOuterAxis m →
                            ∃ n : Fin 8, ePow m (eB m) n.val = x) ∧
                          Nat.card (ZMod 8 ≃+ ZMod 8) = 4 ∧
                            (∀ U : Set (eCarrier m 8),
                              eIsSubgroup m U →
                                Odd (Set.ncard U) →
                                  U ⊆ eRotationAxis m) ∧
                              (∀ U : Set (eCarrier m 8),
                                eIsSubgroup m U →
                                  Set.ncard U = m →
                                    U = eRotationAxis m) ∧
                                (∀ φ : eCarrier m 8 ≃ eCarrier m 8,
                                  eAutomorphism m 8 φ →
                                    Set.image φ (eRotationAxis m) =
                                      eRotationAxis m)

end

end MathlibPlus.Open.ResearchFormalization.R1184StructuralFactsClaim41742
