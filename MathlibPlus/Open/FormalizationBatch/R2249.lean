import Mathlib

namespace MathlibPlus.Open.FormalizationBatch.R2249

open scoped BigOperators

noncomputable section

abbrev G : Type := ZMod 2 × ZMod 2 × ZMod 2 × ZMod 9

def IsInverseAtom (a : Finset G) : Prop :=
  ∃ x : G, x ≠ 0 ∧ a = {x, -x}

abbrev InvAtom : Type := {a : Finset G // IsInverseAtom a}

noncomputable instance instFintypeInvAtom : Fintype InvAtom := Fintype.ofFinite _

def atomMap (e : AddEquiv G G) (a : InvAtom) : InvAtom :=
  ⟨a.1.image e, by
    rcases a.2 with ⟨x, hx, hax⟩
    refine ⟨e x, ?_, ?_⟩
    · intro h
      apply hx
      apply e.injective
      simpa using h
    · rw [hax]
      simp
  ⟩

def atomEquiv (e : AddEquiv G G) : InvAtom ≃ InvAtom where
  toFun := atomMap e
  invFun := atomMap e.symm
  left_inv := by
    intro a
    apply Subtype.ext
    simp [atomMap, Finset.image_image]
  right_inv := by
    intro a
    apply Subtype.ext
    simp [atomMap, Finset.image_image]

abbrev EffectiveAtomAction : Type :=
  {p : InvAtom ≃ InvAtom // ∃ e : AddEquiv G G, p = atomEquiv e}

abbrev SingletonAtom : Type := {a : InvAtom // a.1.card = 1}
abbrev PairAtom : Type := {a : InvAtom // a.1.card = 2}

noncomputable instance instFintypeEffectiveAtomAction : Fintype EffectiveAtomAction := Fintype.ofFinite _
noncomputable instance instFintypeSingletonAtom : Fintype SingletonAtom := Fintype.ofFinite _
noncomputable instance instFintypePairAtom : Fintype PairAtom := Fintype.ofFinite _

def IsConnectionSet (S : Finset G) : Prop :=
  0 ∉ S ∧ ∀ x : G, x ∈ S ↔ -x ∈ S

abbrev ConnectionSet : Type := {S : Finset G // IsConnectionSet S}
abbrev Connection33 : Type := {S : ConnectionSet // S.1.card = 33}

def nonidentityComplement (S : Connection33) : Finset G :=
  (Finset.univ.erase 0) \ S.1.1

noncomputable instance instFintypeConnectionSet : Fintype ConnectionSet := Fintype.ofFinite _
noncomputable instance instFintypeConnection33 : Fintype Connection33 := Fintype.ofFinite _

def mapConnection (e : AddEquiv G G) (S : ConnectionSet) : ConnectionSet :=
  ⟨S.1.image e, by
    constructor
    · intro h
      rcases Finset.mem_image.mp h with ⟨x, hx, hzero⟩
      apply S.2.1
      have hxzero : x = 0 := e.injective (by simpa using hzero)
      exact hxzero ▸ hx
    · intro y
      constructor
      · intro hy
        rcases Finset.mem_image.mp hy with ⟨x, hx, hxy⟩
        refine Finset.mem_image.mpr ⟨-x, (S.2.2 x).mp hx, ?_⟩
        simpa [hxy]
      · intro hy
        rcases Finset.mem_image.mp hy with ⟨x, hx, hxy⟩
        refine Finset.mem_image.mpr ⟨-x, (S.2.2 x).mp hx, ?_⟩
        simpa using congrArg Neg.neg hxy
  ⟩

def mapConn33 (e : AddEquiv G G) (S : Connection33) : Connection33 :=
  ⟨mapConnection e S.1, by
    have hcard : (mapConnection e S.1).1.card = S.1.1.card := by
      exact Finset.card_image_of_injective S.1.1 e.injective
    exact hcard.trans S.2
  ⟩

lemma mapConnection_comp (e f : AddEquiv G G) (S : ConnectionSet) :
    mapConnection f (mapConnection e S) = mapConnection (e.trans f) S := by
  apply Subtype.ext
  simp [mapConnection, Finset.image_image]

lemma mapConnection_symm (e : AddEquiv G G) (S : ConnectionSet) :
    mapConnection e.symm (mapConnection e S) = S := by
  apply Subtype.ext
  simp [mapConnection, Finset.image_image]

lemma mapConn33_comp (e f : AddEquiv G G) (S : Connection33) :
    mapConn33 f (mapConn33 e S) = mapConn33 (e.trans f) S := by
  apply Subtype.ext
  simp [mapConn33, mapConnection, Finset.image_image]

lemma mapConn33_symm (e : AddEquiv G G) (S : Connection33) :
    mapConn33 e.symm (mapConn33 e S) = S := by
  apply Subtype.ext
  simp [mapConn33, mapConnection, Finset.image_image]

def ConnectionOrbitRel (S T : Connection33) : Prop :=
  ∃ e : AddEquiv G G, mapConn33 e S = T

instance connectionSetoid : Setoid Connection33 where
  r := ConnectionOrbitRel
  iseqv := by
    constructor
    · intro S
      exact ⟨AddEquiv.refl G, by
        apply Subtype.ext
        simp [mapConn33, mapConnection]
      ⟩
    · intro S T h
      rcases h with ⟨e, h⟩
      refine ⟨e.symm, ?_⟩
      rw [← h]
      exact mapConn33_symm e S
    · intro S T U hST hTU
      rcases hST with ⟨e, hST⟩
      rcases hTU with ⟨f, hTU⟩
      refine ⟨e.trans f, ?_⟩
      calc
        mapConn33 (e.trans f) S = mapConn33 f (mapConn33 e S) := (mapConn33_comp e f S).symm
        _ = mapConn33 f T := by rw [hST]
        _ = U := hTU

abbrev FixedConnection (e : AddEquiv G G) : Type :=
  {S : Connection33 // mapConn33 e S = S}

noncomputable instance instFintypeFixedConnection (e : AddEquiv G G) : Fintype (FixedConnection e) := Fintype.ofFinite _

def singletonCount (S : Connection33) : Nat :=
  (S.1.1.filter (fun x => x ≠ 0 ∧ -x = x)).card

abbrev Layer (s : Nat) : Type := {S : Connection33 // singletonCount S = s}

noncomputable instance instFintypeLayer (s : Nat) : Fintype (Layer s) := Fintype.ofFinite _

def LayerOrbitRel {s : Nat} (S T : Layer s) : Prop :=
  ∃ e : AddEquiv G G, mapConn33 e S.1 = T.1

instance layerSetoid (s : Nat) : Setoid (Layer s) where
  r := LayerOrbitRel
  iseqv := by
    constructor
    · intro S
      exact ⟨AddEquiv.refl G, by
        apply Subtype.ext
        simp [mapConn33, mapConnection]
      ⟩
    · intro S T h
      rcases h with ⟨e, h⟩
      refine ⟨e.symm, ?_⟩
      rw [← h]
      exact mapConn33_symm e S.1
    · intro S T U hST hTU
      rcases hST with ⟨e, hST⟩
      rcases hTU with ⟨f, hTU⟩
      refine ⟨e.trans f, ?_⟩
      calc
        mapConn33 (e.trans f) S.1 = mapConn33 f (mapConn33 e S.1) := (mapConn33_comp e f S.1).symm
        _ = mapConn33 f T.1 := by rw [hST]
        _ = U.1 := hTU

noncomputable instance instFintypeConnectionQuotient : Fintype (Quotient (inferInstance : Setoid Connection33)) := Fintype.ofFinite _
noncomputable instance instFintypeLayerQuotient (s : Nat) : Fintype (Quotient (inferInstance : Setoid (Layer s))) := Fintype.ofFinite _

def claim_44363 : Prop :=
  Fintype.card G = 72 ∧
  (∀ S : Connection33, (nonidentityComplement S).card = 38) ∧
  Fintype.card (AddEquiv G G) = 1008 ∧
  Fintype.card EffectiveAtomAction = 504 ∧
  Fintype.card SingletonAtom = 7 ∧
  Fintype.card PairAtom = 32 ∧
  Fintype.card Connection33 = 34255379130 ∧
  (∑ e : AddEquiv G G, Fintype.card (FixedConnection e)) = 34845778800 ∧
  Fintype.card (Quotient (inferInstance : Setoid Connection33)) = 69138450 ∧
  Fintype.card (Quotient (inferInstance : Setoid (Layer 1))) = 8587484 ∧
  Fintype.card (Quotient (inferInstance : Setoid (Layer 3))) = 39822374 ∧
  Fintype.card (Quotient (inferInstance : Setoid (Layer 5))) = 19982742 ∧
  Fintype.card (Quotient (inferInstance : Setoid (Layer 7))) = 745850

end

end MathlibPlus.Open.FormalizationBatch.R2249
