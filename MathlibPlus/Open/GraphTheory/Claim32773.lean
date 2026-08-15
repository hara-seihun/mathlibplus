import Mathlib

open BigOperators

namespace MathlibPlus.Open.GraphTheory.Claim32773

/-- The group C₂³ × C₉, written additively. -/
abbrev G := (ZMod 2 × ZMod 2 × ZMod 2) × ZMod 9

/-- The inverse orbit of a group element. -/
def inverseOrbit (g : G) : Finset G := {g, -g}

/-- The nonidentity elements and their inverse atoms. -/
def NonidentityElement := {g : G // g ≠ 0}

noncomputable instance : Fintype NonidentityElement :=
  Fintype.ofInjective (fun g : NonidentityElement => g.1) Subtype.val_injective

def InverseAtom :=
  {s : Finset G // ∃ g : G, g ≠ 0 ∧ s = inverseOrbit g}

noncomputable instance : Fintype InverseAtom :=
  Fintype.ofInjective (fun s : InverseAtom => s.1) Subtype.val_injective

/-- Singleton inverse atoms and paired inverse atoms. -/
def SingletonInverseAtom := {s : InverseAtom // s.1.card = 1}
def PairedInverseAtom := {s : InverseAtom // s.1.card = 2}

noncomputable instance : Fintype SingletonInverseAtom :=
  Fintype.ofInjective (fun s : SingletonInverseAtom => s.1) Subtype.val_injective

noncomputable instance : Fintype PairedInverseAtom :=
  Fintype.ofInjective (fun s : PairedInverseAtom => s.1) Subtype.val_injective

/-- The action of an automorphism on inverse atoms. -/
def atomMap (φ : G ≃+ G) (s : InverseAtom) : InverseAtom := by
  refine ⟨s.1.image φ, ?_⟩
  rcases s.2 with ⟨g, hg, hs⟩
  refine ⟨φ g, ?_, ?_⟩
  · intro h
    apply hg
    have h' : φ g = φ 0 := by simpa using h
    exact φ.injective h'
  · rw [hs]
    ext x
    simp [inverseOrbit, φ.map_neg]

/-- The induced permutation of inverse atoms. -/
def inverseAtomAction (φ : G ≃+ G) : InverseAtom ≃ InverseAtom :=
  { toFun := atomMap φ
    invFun := atomMap φ.symm
    left_inv := by
      intro s
      rcases s.2 with ⟨g, hg, hs⟩
      apply Subtype.ext
      change (s.1.image φ).image φ.symm = s.1
      rw [hs]
      ext x
      simp [inverseOrbit]
    right_inv := by
      intro s
      rcases s.2 with ⟨g, hg, hs⟩
      apply Subtype.ext
      change (s.1.image φ.symm).image φ = s.1
      rw [hs]
      ext x
      simp [inverseOrbit]
  }

/-- Inversion on the C₉ coordinate. -/
def c9CoordinateInversion : G ≃+ G :=
  { toFun := fun g => (g.1, -g.2)
    invFun := fun g => (g.1, -g.2)
    left_inv := by intro g; simp
    right_inv := by intro g; simp
    map_add' := by
      intro g h
      ext <;> simp [add_comm] }

/-- An ordinary undirected Cayley connection set. -/
structure OrdinaryConnectionSet where
  carrier : Finset G
  avoidsIdentity : 0 ∉ carrier
  inverseClosed : ∀ g : G, g ∈ carrier ↔ -g ∈ carrier

def connectionSetValency (S : OrdinaryConnectionSet) : ℕ := S.carrier.card

/-- The inverse-atom count, action kernel, image, and connection-set description. -/
def inverseAtomsAndConnectionSets_claim32773 : Prop := by
  classical
  exact
    Fintype.card G = 72 ∧
    Fintype.card NonidentityElement = 71 ∧
    Fintype.card SingletonInverseAtom = 7 ∧
    Fintype.card PairedInverseAtom = 32 ∧
    Fintype.card (G ≃+ G) = 1008 ∧
    (∀ φ : G ≃+ G,
      inverseAtomAction φ = Equiv.refl _ ↔
        φ = AddEquiv.refl G ∨ φ = c9CoordinateInversion) ∧
    (Finset.univ.image (fun φ : G ≃+ G => inverseAtomAction φ)).card = 504 ∧
    (∀ S : OrdinaryConnectionSet,
      0 ∉ S.carrier ∧
        (∀ g : G, g ∈ S.carrier ↔ -g ∈ S.carrier) ∧
        connectionSetValency S = S.carrier.card)

end MathlibPlus.Open.GraphTheory.Claim32773
