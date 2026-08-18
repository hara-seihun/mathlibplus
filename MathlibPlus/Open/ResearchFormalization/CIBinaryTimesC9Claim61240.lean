import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.CIBinaryTimesC9Claim61240

noncomputable section

abbrev C9 := ZMod 9
abbrev BinarySpace (r : ℕ) := Fin r → ZMod 2
abbrev CayleyCarrier (r : ℕ) := BinarySpace r × C9

def awayFromZero {r : ℕ} (S : Set (CayleyCarrier r)) : Prop :=
  S ⊆ {g | g ≠ 0}

def inverseClosed {r : ℕ} (S : Set (CayleyCarrier r)) : Prop :=
  ∀ x, x ∈ S → -x ∈ S

def cayleyAdjacency {r : ℕ} (S : Set (CayleyCarrier r))
    (x y : CayleyCarrier r) : Prop :=
  x ≠ y ∧ y - x ∈ S

def plusMinusThree : Set C9 :=
  {z | z = (3 : C9) ∨ z = -(3 : C9)}

def zeroPlusMinusThree : Set C9 :=
  {z | z = (0 : C9) ∨ z = (3 : C9) ∨ z = -(3 : C9)}

def flexibleSection (D : Set C9) : Prop :=
  D = ∅ ∨
    D = Set.univ ∨
    D = ({0} : Set C9) ∨
    D = Set.univ \ ({0} : Set C9) ∨
    D = plusMinusThree ∨
    D = Set.univ \ plusMinusThree ∨
    D = zeroPlusMinusThree ∨
    D = Set.univ \ zeroPlusMinusThree

def coarseSection (D : Set C9) : Prop :=
  D = ∅ ∨
    D = Set.univ ∨
    D = zeroPlusMinusThree ∨
    D = Set.univ \ zeroPlusMinusThree

def sectionSet {r : ℕ} (S : Set (CayleyCarrier r))
    (v : BinarySpace r) : Set C9 :=
  {z | (v, z) ∈ S}

def nonFlexibleDirections {r : ℕ}
    (S : Set (CayleyCarrier r)) : Set (BinarySpace r) :=
  {v | v ≠ 0 ∧ ¬ flexibleSection (sectionSet S v)}

def nonCoarseDirections {r : ℕ}
    (S : Set (CayleyCarrier r)) : Set (BinarySpace r) :=
  {v | v ≠ 0 ∧ ¬ coarseSection (sectionSet S v)}

def directionSpan {r : ℕ} (S : Set (CayleyCarrier r)) :
    Submodule (ZMod 2) (BinarySpace r) :=
  Submodule.span (ZMod 2) (nonCoarseDirections S)

def fibrePreservingPointedGraphIso {r : ℕ}
    (S T : Set (CayleyCarrier r))
    (f : CayleyCarrier r ≃ CayleyCarrier r)
    (beta : BinarySpace r ≃ BinarySpace r)
    (sigma : BinarySpace r → C9 ≃ C9) : Prop :=
  f 0 = 0 ∧
    (∀ x z, f (x, z) = (beta x, sigma x z)) ∧
    (∀ x y,
      cayleyAdjacency S x y ↔ cayleyAdjacency T (f x) (f y))

def groupAutomorphismTransport {r : ℕ}
    (S T : Set (CayleyCarrier r)) : Prop :=
  ∃ alpha : CayleyCarrier r ≃+ CayleyCarrier r,
    alpha '' S = T

def affineCosetConclusion {r : ℕ}
    (S T : Set (CayleyCarrier r))
    (sigma : BinarySpace r → C9 ≃ C9) : Prop :=
  ∃ u : BinarySpace r → C9ˣ,
    ∃ c : BinarySpace r → C9,
      (∀ x z, sigma x z = (u x : C9) * z + c x) ∧
      (∀ x y, y - x ∈ directionSpan S → u x = u y) ∧
      (∀ v, v ∉ directionSpan S →
        coarseSection (sectionSet S v)) ∧
      (directionSpan S = ⊤ → groupAutomorphismTransport S T)

def claim61240 : Prop :=
  ∀ r : ℕ,
    (r = 3 ∨ r = 4 ∨ r = 5) →
      ∀ S T : Set (CayleyCarrier r),
        awayFromZero S →
        awayFromZero T →
        inverseClosed S →
        inverseClosed T →
        ∀ f : CayleyCarrier r ≃ CayleyCarrier r,
          ∀ beta : BinarySpace r ≃ BinarySpace r,
            ∀ sigma : BinarySpace r → C9 ≃ C9,
              fibrePreservingPointedGraphIso S T f beta sigma →
                let R := nonFlexibleDirections S
                let A := nonCoarseDirections S
                let W := Submodule.span (ZMod 2) A
                (R = ∅ → groupAutomorphismTransport S T) ∧
                (R ≠ ∅ →
                  affineCosetConclusion S T sigma ∧
                  (¬ groupAutomorphismTransport S T →
                    R ≠ ∅ ∧
                      (⊥ : Submodule (ZMod 2) (BinarySpace r)) < W ∧
                      W < (⊤ : Submodule (ZMod 2) (BinarySpace r))))

end

end MathlibPlus.Open.ResearchFormalization.CIBinaryTimesC9Claim61240
