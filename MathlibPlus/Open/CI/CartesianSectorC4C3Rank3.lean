import Mathlib

namespace MathlibPlus.Open.CartesianSectorC4C3Rank3

abbrev V := Fin 3 → ZMod 3
abbrev G := ZMod 4 × V

 def inverseClosed {H : Type*} [Neg H] (R : Finset H) : Prop :=
  ∀ x, x ∈ R ↔ -x ∈ R

def identityFree {H : Type*} [Zero H] (R : Finset H) : Prop :=
  (0 : H) ∉ R

def spansV (U : Finset V) : Prop :=
  Submodule.span (ZMod 3) (U : Set V) = ⊤

def eligible (U : Finset V) : Prop :=
  inverseClosed U ∧ (0 : V) ∉ U ∧ spansV U

def isA (A : Finset (ZMod 4)) : Prop :=
  A = ({1, 3} : Finset (ZMod 4)) ∨ A = ({1, 2, 3} : Finset (ZMod 4))

def cartesianSector (A : Finset (ZMod 4)) (U : Finset V) : Finset G :=
  Finset.univ.filter (fun g =>
    (g.1 ∈ A ∧ g.2 = 0) ∨ (g.1 = 0 ∧ g.2 ∈ U))

def cartesianComplement (A : Finset (ZMod 4)) (U : Finset V) : Finset G :=
  (Finset.univ.erase (0, 0)).filter (fun g => g ∉ cartesianSector A U)

def ordinaryCayleyIsomorphism (R T : Finset G) : Prop :=
  ∃ f : G → G,
    Function.Bijective f ∧
      ∀ x y, (y - x) ∈ R ↔ (f y - f x) ∈ T

def ordinaryUndirectedCI (R : Finset G) : Prop :=
  identityFree R ∧ inverseClosed R ∧
    ∀ T : Finset G, identityFree T → inverseClosed T →
      ordinaryCayleyIsomorphism R T →
        ∃ α : G ≃+ G, ∀ x, x ∈ R ↔ α x ∈ T

def directConnectionSet (R : Finset G) : Prop :=
  ∃ A : Finset (ZMod 4), ∃ U : Finset V,
    isA A ∧ eligible U ∧ R = cartesianSector A U

def complementConnectionSet (R : Finset G) : Prop :=
  ∃ A : Finset (ZMod 4), ∃ U : Finset V,
    isA A ∧ eligible U ∧ R = cartesianComplement A U

def cartesianSectorClaim : Prop :=
  (Nat.card {U : Finset V // eligible U} = 8035) ∧
    (∀ A : Finset (ZMod 4), ∀ U : Finset V,
      isA A → eligible U →
        ordinaryUndirectedCI (cartesianSector A U) ∧
          ordinaryUndirectedCI (cartesianComplement A U) ∧
          8 ≤ (cartesianSector A U).card ∧
          (cartesianSector A U).card ≤ 29 ∧
          (cartesianSector A U).card % 2 = A.card % 2) ∧
    (Nat.card {R : Finset G // directConnectionSet R} = 16070) ∧
    (Nat.card {R : Finset G // complementConnectionSet R} = 16070) ∧
    (Nat.card {R : Finset G // directConnectionSet R ∨ complementConnectionSet R} = 32140) ∧
    (∀ R, directConnectionSet R → ¬ complementConnectionSet R) ∧
    (∀ R₁ R₂, directConnectionSet R₁ → directConnectionSet R₂ →
      (Finset.univ.erase (0, 0) \ R₁) = (Finset.univ.erase (0, 0) \ R₂) → R₁ = R₂)

end MathlibPlus.Open.CartesianSectorC4C3Rank3
