import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchFinite

noncomputable section

abbrev G27 := ZMod 4 × (ZMod 3 × ZMod 3 × ZMod 3)

def H27 : AddSubgroup G27 :=
  AddSubgroup.prod (⊥ : AddSubgroup (ZMod 4))
    (⊤ : AddSubgroup (ZMod 3 × ZMod 3 × ZMod 3))

def h27CarrierPredicate (x : G27) : Prop := x ∈ H27

def H27Carrier : Type := {x : G27 // h27CarrierPredicate x}

noncomputable instance h27CarrierFintype : Fintype H27Carrier := by
  classical
  exact Fintype.subtype (Finset.univ.filter h27CarrierPredicate) (by simp)

def k27Predicate (K : Finset G27) : Prop :=
  K.card = 27 ∧
    0 ∈ K ∧
    (∀ x ∈ K, ∀ y ∈ K, x + y ∈ K) ∧
    (∀ x ∈ K, -x ∈ K)

def K27 : Type := {K : Finset G27 // k27Predicate K}

noncomputable instance k27Fintype : Fintype K27 := by
  classical
  exact Fintype.subtype (Finset.univ.filter k27Predicate) (by simp)

def sameK27Orbit (K L : K27) : Prop :=
  ∃ e : G27 ≃+ G27, ∀ x : G27,
    x ∈ e '' (K.1 : Set G27) ↔ x ∈ (L.1 : Set G27)

/-- Claim 44373: the intrinsic order-27 block subgroup has quotient C4 and
forms one automorphism orbit. -/
def claim_44373 : Prop :=
  Fintype.card H27Carrier = 27 ∧
    Fintype.card (ZMod 4) = 4 ∧
    Nonempty ((G27 ⧸ H27) ≃+ ZMod 4) ∧
    Nonempty K27 ∧
    (∃ K : K27, ∀ x : G27,
      x ∈ (K.1 : Set G27) ↔ x ∈ H27) ∧
    (∀ K L : K27, sameK27Orbit K L)

def inverseAtom27 (g : G27) : Finset G27 := {g, -g}

def atom27Predicate (s : Finset G27) : Prop :=
  s.Nonempty ∧
    (∀ x ∈ s, x ≠ 0) ∧
    (∀ x : G27, x ∈ s ↔ -x ∈ s) ∧
    (∃ g : G27, s = inverseAtom27 g)

def Atom27 : Type := {s : Finset G27 // atom27Predicate s}

noncomputable instance atom27Fintype : Fintype Atom27 := by
  classical
  exact Fintype.subtype (Finset.univ.filter atom27Predicate) (by simp)

def atomIdentity27 (a : Atom27) : Prop :=
  ∀ g ∈ a.1, g.1 = 0

def atomInvolution27 (a : Atom27) : Prop :=
  ∀ g ∈ a.1, g.1 = 2

def atomOrderFour27 (a : Atom27) : Prop :=
  ∀ g ∈ a.1, g.1 = 1 ∨ g.1 = 3

noncomputable instance atomIdentity27Fintype :
    Fintype {a : Atom27 // atomIdentity27 a} := by
  classical
  exact Fintype.subtype (Finset.univ.filter atomIdentity27) (by simp)

noncomputable instance atomInvolution27Fintype :
    Fintype {a : Atom27 // atomInvolution27 a} := by
  classical
  exact Fintype.subtype (Finset.univ.filter atomInvolution27) (by simp)

noncomputable instance atomOrderFour27Fintype :
    Fintype {a : Atom27 // atomOrderFour27 a} := by
  classical
  exact Fintype.subtype (Finset.univ.filter atomOrderFour27) (by simp)

def inverseClosedConnection27 (S : Finset G27) : Prop :=
  0 ∉ S ∧ ∀ g : G27, g ∈ S ↔ -g ∈ S

noncomputable instance connection27Fintype :
    Fintype {S : Finset G27 // inverseClosedConnection27 S} := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter inverseClosedConnection27) (by simp)

/-- Claim 44377: inversion has the three stated atom populations, with 54
atoms and the corresponding full inverse-closed connection space. -/
def claim_44377 : Prop :=
  (∀ a : Atom27,
    atomIdentity27 a ∨ atomInvolution27 a ∨ atomOrderFour27 a) ∧
    (∀ a : Atom27, ¬(atomIdentity27 a ∧ atomInvolution27 a)) ∧
    (∀ a : Atom27, ¬(atomIdentity27 a ∧ atomOrderFour27 a)) ∧
    (∀ a : Atom27, ¬(atomInvolution27 a ∧ atomOrderFour27 a)) ∧
    Fintype.card {a : Atom27 // atomIdentity27 a} = 13 ∧
    Fintype.card {a : Atom27 // atomInvolution27 a} = 14 ∧
    Fintype.card {a : Atom27 // atomOrderFour27 a} = 27 ∧
    Fintype.card Atom27 = 54 ∧
    Fintype.card {S : Finset G27 // inverseClosedConnection27 S} = 2 ^ 54 ∧
    (2 : Nat) ^ 54 = 18014398509481984

end

end MathlibPlus.Open.ResearchFormalization.BatchFinite
