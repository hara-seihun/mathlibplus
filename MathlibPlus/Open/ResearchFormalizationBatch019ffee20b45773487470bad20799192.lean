import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1647

abbrev G := ZMod 4 × (Fin 3 → ZMod 3)
abbrev V := Fin 3 → ZMod 3

abbrev C4Subgroup := AddSubgroup (ZMod 4)
abbrev VSubgroup := AddSubgroup V

noncomputable def subgroupCard (H : AddSubgroup G) : Nat := Nat.card H

noncomputable def fourSubgroupCard (K : C4Subgroup) : Nat := Nat.card K

noncomputable def threeSubgroupCard (W : VSubgroup) : Nat := Nat.card W

def subgroupProduct (K : C4Subgroup) (W : VSubgroup) : AddSubgroup G := K.prod W

def intrinsicSubgroupDecomposition : Prop :=
  ∀ H : AddSubgroup G,
    subgroupCard H = 2 ∨ subgroupCard H = 3 ∨ subgroupCard H = 6 ∨
      subgroupCard H = 9 ∨ subgroupCard H = 12 ∨ subgroupCard H = 18 →
    (∃ K : C4Subgroup, ∃ W : VSubgroup,
      (fourSubgroupCard K = 2 ∧ threeSubgroupCard W = 1) ∧
        H = subgroupProduct K W ∧
        (∀ K' : C4Subgroup, fourSubgroupCard K' = 2 → K' = K)) ∨
    (∃ K : C4Subgroup, ∃ W : VSubgroup,
      (fourSubgroupCard K = 1 ∧ threeSubgroupCard W = 3) ∧
        H = subgroupProduct K W ∧
        (∀ K' : C4Subgroup, fourSubgroupCard K' = 1 → K' = K)) ∨
    (∃ K : C4Subgroup, ∃ W : VSubgroup,
      (fourSubgroupCard K = 2 ∧ threeSubgroupCard W = 3) ∧
        H = subgroupProduct K W ∧
        (∀ K' : C4Subgroup, fourSubgroupCard K' = 2 → K' = K)) ∨
    (∃ K : C4Subgroup, ∃ W : VSubgroup,
      (fourSubgroupCard K = 1 ∧ threeSubgroupCard W = 9) ∧
        H = subgroupProduct K W ∧
        (∀ K' : C4Subgroup, fourSubgroupCard K' = 1 → K' = K)) ∨
    (∃ K : C4Subgroup, ∃ W : VSubgroup,
      (fourSubgroupCard K = 4 ∧ threeSubgroupCard W = 3) ∧
        H = subgroupProduct K W ∧
        (∀ K' : C4Subgroup, fourSubgroupCard K' = 4 → K' = K)) ∨
    (∃ K : C4Subgroup, ∃ W : VSubgroup,
      (fourSubgroupCard K = 2 ∧ threeSubgroupCard W = 9) ∧
        H = subgroupProduct K W ∧
        (∀ K' : C4Subgroup, fourSubgroupCard K' = 2 → K' = K))

def grassmannian (d : ℕ) : Type :=
  {W : Submodule (ZMod 3) V // Module.finrank (ZMod 3) W = d}

abbrev GL3 := V ≃ₗ[ZMod 3] V

def gl3TransitiveOnFixedDimension : Prop :=
  Nat.card (grassmannian 0) = 1 ∧
  Nat.card (grassmannian 1) = 13 ∧
  Nat.card (grassmannian 2) = 13 ∧
  Nat.card GL3 = 11232 ∧
  ∀ {W W' : Submodule (ZMod 3) V},
    Module.finrank (ZMod 3) W = Module.finrank (ZMod 3) W' →
    ∃ e : GL3, Submodule.map e.toLinearMap W = W'

def extensionSplits (H : AddSubgroup G) : Prop :=
  Nonempty ((H × (G ⧸ H)) ≃+ G)

def cyclicFourExtensionIsNotElementary : Prop :=
  ¬ Nonempty ((ZMod 2 × ZMod 2) ≃+ ZMod 4)

def splitVersusNonsplitMediumExtensions : Prop :=
  (∀ H : AddSubgroup G,
      subgroupCard H = 3 ∨ subgroupCard H = 9 ∨ subgroupCard H = 12 →
        extensionSplits H) ∧
  (∀ H : AddSubgroup G,
      subgroupCard H = 2 ∨ subgroupCard H = 6 ∨ subgroupCard H = 18 →
        ¬ extensionSplits H) ∧
  cyclicFourExtensionIsNotElementary

def intrinsicSubgroupsAndGrassmannCounts : Prop :=
  intrinsicSubgroupDecomposition ∧ gl3TransitiveOnFixedDimension

abbrev D3 := ZMod 3
abbrev BlockH := ZMod 4 × (Fin 2 → ZMod 3)
abbrev BlockG := D3 × BlockH

def fiberCount (S : Finset BlockG) (h : BlockH) : Nat :=
  (S.filter (fun x => x.2 = h)).card

def quotientRelationTupleIso (c₁ c₂ : BlockH → Nat) : Prop :=
  ∃ q : BlockH ≃ BlockH, ∀ a b : BlockH,
    c₁ (b - a) = c₂ (q b - q a)

def blockPreservingCayleyGraphIsomorphism
    (S T : Finset BlockG) : Prop :=
  ∃ f : BlockG ≃ BlockG, ∃ q : BlockH ≃ BlockH,
    (∀ d : D3, ∀ h : BlockH, (f (d, h)).2 = q h) ∧
    (∀ x y : BlockG, y - x ∈ S ↔ f y - f x ∈ T)

def quotientValencyTupleInvariant : Prop :=
  ∀ S T : Finset BlockG,
    blockPreservingCayleyGraphIsomorphism S T →
      (∀ h : BlockH, fiberCount S h ≤ 3 ∧ fiberCount T h ≤ 3) ∧
      quotientRelationTupleIso (fiberCount S) (fiberCount T)

end MathlibPlus.Open.ResearchFormalization.R1647

namespace MathlibPlus.Open.ResearchFormalization.R1648

abbrev G := (Fin 3 → ZMod 2) × (Fin 2 → ZMod 3)

noncomputable def inverseClosed (S : Finset G) : Prop :=
  ∀ x : G, x ∈ S ↔ -x ∈ S

def isConnectionSet (k : Nat) (S : Finset G) : Prop :=
  0 ∉ S ∧ S.card = k ∧ inverseClosed S

def singletonAtomCount (S : Finset G) : Nat :=
  (S.filter (fun x => x = -x)).card

def pairAtomCount (S : Finset G) : Nat :=
  (S.filter (fun x => x ≠ -x)).card / 2

def valency19Stratum (singletons pairs : Nat) : Type :=
  {S : Finset G // isConnectionSet 19 S ∧
    singletonAtomCount S = singletons ∧ pairAtomCount S = pairs}

def valency20Stratum (singletons pairs : Nat) : Type :=
  {S : Finset G // isConnectionSet 20 S ∧
    singletonAtomCount S = singletons ∧ pairAtomCount S = pairs}

noncomputable def valency19ConnectionSetStrata : Prop :=
  Nat.card {S : Finset G // isConnectionSet 19 S} = 636071268 ∧
  (∀ S : Finset G, isConnectionSet 19 S →
    (singletonAtomCount S = 1 ∧ pairAtomCount S = 9) ∨
    (singletonAtomCount S = 3 ∧ pairAtomCount S = 8) ∨
    (singletonAtomCount S = 5 ∧ pairAtomCount S = 7) ∨
    (singletonAtomCount S = 7 ∧ pairAtomCount S = 6)) ∧
  Nat.card (valency19Stratum 1 9) = 196341600 ∧
  Nat.card (valency19Stratum 3 8) = 368140500 ∧
  Nat.card (valency19Stratum 5 7) = 70682976 ∧
  Nat.card (valency19Stratum 7 6) = 906192 ∧
  Nat.card (valency19Stratum 1 9) +
      Nat.card (valency19Stratum 3 8) +
      Nat.card (valency19Stratum 5 7) +
      Nat.card (valency19Stratum 7 6) = 636071268

noncomputable def valency20ConnectionSetStrata : Prop :=
  Nat.card {S : Finset G // isConnectionSet 20 S} = 1045238532 ∧
  (∀ S : Finset G, isConnectionSet 20 S →
    (singletonAtomCount S = 0 ∧ pairAtomCount S = 10) ∨
    (singletonAtomCount S = 2 ∧ pairAtomCount S = 9) ∨
    (singletonAtomCount S = 4 ∧ pairAtomCount S = 8) ∨
    (singletonAtomCount S = 6 ∧ pairAtomCount S = 7)) ∧
  Nat.card (valency20Stratum 0 10) = 64512240 ∧
  Nat.card (valency20Stratum 2 9) = 589024800 ∧
  Nat.card (valency20Stratum 4 8) = 368140500 ∧
  Nat.card (valency20Stratum 6 7) = 23560992 ∧
  Nat.card (valency20Stratum 0 10) +
      Nat.card (valency20Stratum 2 9) +
      Nat.card (valency20Stratum 4 8) +
      Nat.card (valency20Stratum 6 7) = 1045238532

def cayleyGraphIsomorphism (S T : Finset G) : Prop :=
  ∃ e : G ≃ G, ∀ x y : G,
    (y - x ∈ S ↔ e y - e x ∈ T)

def groupAutomorphismCarries (S T : Finset G) : Prop :=
  ∃ e : G ≃+ G, ∀ x : G, x ∈ S ↔ e x ∈ T

def isCIAtValency (k : Nat) : Prop :=
  ∀ ⦃S T : Finset G⦄,
    isConnectionSet k S → isConnectionSet k T →
      cayleyGraphIsomorphism S T → groupAutomorphismCarries S T

def nonidentityComplement (S : Finset G) : Finset G :=
  (Finset.univ.erase (0 : G)) \ S

def cayleyConnected (S : Finset G) : Prop :=
  ∀ x y : G, Relation.ReflTransGen (fun a b : G => b - a ∈ S) x y

def presentationOrbitRepresentatives (R : Finset (Finset G)) : Prop :=
  R.card = 186405 ∧
  (∀ T ∈ R, isConnectionSet 19 T) ∧
  (∀ S : Finset G, isConnectionSet 19 S →
    ∃ T ∈ R, groupAutomorphismCarries S T) ∧
  (∀ T₁ T₂ : Finset G, T₁ ∈ R → T₂ ∈ R →
    groupAutomorphismCarries T₁ T₂ → T₁ = T₂)

def graphOrbitRepresentatives (R : Finset (Finset G)) : Prop :=
  R.card = 186405 ∧
  (∀ T ∈ R, isConnectionSet 19 T) ∧
  (∀ S : Finset G, isConnectionSet 19 S →
    ∃ T ∈ R, cayleyGraphIsomorphism S T) ∧
  (∀ T₁ T₂ : Finset G, T₁ ∈ R → T₂ ∈ R →
    cayleyGraphIsomorphism T₁ T₂ → T₁ = T₂)

def connectedGraphOrbitRepresentatives (R : Finset (Finset G)) : Prop :=
  R.card = 185889 ∧
  (∀ T ∈ R, isConnectionSet 19 T ∧ cayleyConnected T) ∧
  (∀ S : Finset G, isConnectionSet 19 S → cayleyConnected S →
    ∃ T ∈ R, cayleyGraphIsomorphism S T) ∧
  (∀ T₁ T₂ : Finset G, T₁ ∈ R → T₂ ∈ R →
    cayleyGraphIsomorphism T₁ T₂ → T₁ = T₂)

noncomputable def valency19PresentationAndGraphTypes : Prop :=
  Nat.card {S : Finset G // isConnectionSet 19 S} = 636071268 ∧
  Nat.card (G ≃+ G) = 8064 ∧
  (∃ R : Finset (Finset G), presentationOrbitRepresentatives R) ∧
  (∃ R : Finset (Finset G), graphOrbitRepresentatives R) ∧
  (∃ R : Finset (Finset G), connectedGraphOrbitRepresentatives R) ∧
  (∀ ⦃S T : Finset G⦄,
    isConnectionSet 19 S → isConnectionSet 19 T →
      (cayleyGraphIsomorphism S T ↔ groupAutomorphismCarries S T))

def valencies19And52AreCI : Prop :=
  Nat.card {x : G // x ≠ 0} = 71 ∧
  isCIAtValency 19 ∧
  isCIAtValency 52 ∧
  (∀ S : Finset G, isConnectionSet 19 S →
    isConnectionSet 52 (nonidentityComplement S)) ∧
  (∀ ⦃S T : Finset G⦄,
    isConnectionSet 19 S → isConnectionSet 19 T →
      (cayleyGraphIsomorphism S T ↔
        cayleyGraphIsomorphism (nonidentityComplement S)
          (nonidentityComplement T)) ∧
      (groupAutomorphismCarries S T ↔
        groupAutomorphismCarries (nonidentityComplement S)
          (nonidentityComplement T)))

end MathlibPlus.Open.ResearchFormalization.R1648
