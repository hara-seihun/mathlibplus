import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim61234

noncomputable section

abbrev C9 := ZMod 9
abbrev BinarySpace (r : ℕ) := Fin r → ZMod 2
abbrev CayleyCarrier (r : ℕ) := BinarySpace r × C9
abbrev BipartiteCarrier := Fin 2 × C9

/-- Inverse closure for a subset of the cyclic-nine group. -/
def inverseClosedSet (D : Set C9) : Prop :=
  ∀ z, z ∈ D ↔ -z ∈ D

/-- The eight cyclic-nine sections singled out as flexible. -/
def plusMinusThree : Set C9 :=
  {z | z = (3 : C9) ∨ z = -(3 : C9)}

def zeroPlusMinusThree : Set C9 :=
  {z | z = 0 ∨ z = (3 : C9) ∨ z = -(3 : C9)}

def flexibleSection (D : Set C9) : Prop :=
  D = ∅ ∨
    D = Set.univ ∨
    D = ({0} : Set C9) ∨
    D = Set.univ \ ({0} : Set C9) ∨
    D = plusMinusThree ∨
    D = Set.univ \ plusMinusThree ∨
    D = zeroPlusMinusThree ∨
    D = Set.univ \ zeroPlusMinusThree

/-- The two-coloured bipartite Cayley relation on distinguished copies of C9. -/
def bipartiteAdj (D : Set C9)
    (x y : BipartiteCarrier) : Prop :=
  x.1 = 0 ∧ y.1 = 1 ∧ y.2 - x.2 ∈ D

def colorPreserving (e : Equiv.Perm BipartiteCarrier) : Prop :=
  ∀ x, (e x).1 = x.1

def bipartiteIso (D E : Set C9)
    (e : Equiv.Perm BipartiteCarrier) : Prop :=
  colorPreserving e ∧
    ∀ x y, bipartiteAdj D x y ↔ bipartiteAdj E (e x) (e y)

/-- The affine pair map with one unit multiplier on both colour classes. -/
def affinePairMap (u : C9ˣ) (c d : C9)
    (x : BipartiteCarrier) : BipartiteCarrier :=
  (x.1, (u : C9) * x.2 + if x.1 = 0 then c else d)

def affinePairCondition (D E : Set C9)
    (u : C9ˣ) (c d : C9) : Prop :=
  Set.image (fun z : C9 => (u : C9) * z + d - c) D = E

def affinePairIso (D E : Set C9) : Prop :=
  ∃ u : C9ˣ, ∃ c d : C9,
    affinePairCondition D E u c d

/-- Exact colour-preserving affine rigidity for every nonflexible cyclic-nine
section, including the eight exceptional inverse-closed sections. -/
def cyclicNineBipartiteRigidity : Prop :=
  Nat.card {D : Set C9 // inverseClosedSet D} = 32 ∧
    Nat.card {D : Set C9 // flexibleSection D} = 8 ∧
    (∀ D : Set C9, flexibleSection D → inverseClosedSet D) ∧
    (∀ D : Set C9, inverseClosedSet D → ¬ flexibleSection D →
      ∀ e : Equiv.Perm BipartiteCarrier,
        bipartiteIso D D e ↔
          ∃ u : C9ˣ, ∃ c d : C9,
            affinePairCondition D D u c d ∧
              ∀ x, e x = affinePairMap u c d x) ∧
    ∀ D : Set C9, inverseClosedSet D → ¬ flexibleSection D →
      ∀ E : Set C9, inverseClosedSet E →
        ((∃ e : Equiv.Perm BipartiteCarrier, bipartiteIso D E e) ↔
          affinePairIso D E) ∧
        ∀ e : Equiv.Perm BipartiteCarrier,
          bipartiteIso D E e →
            ∃ u : C9ˣ, ∃ c d : C9,
              affinePairCondition D E u c d ∧
                ∀ x, e x = affinePairMap u c d x

/-- The connection section over a binary direction. -/
def sectionSet {r : ℕ} (S : Set (CayleyCarrier r))
    (v : BinarySpace r) : Set C9 :=
  {z | (v, z) ∈ S}

def identityFree {r : ℕ} (S : Set (CayleyCarrier r)) : Prop :=
  (0 : CayleyCarrier r) ∉ S

def inverseClosed {r : ℕ} (S : Set (CayleyCarrier r)) : Prop :=
  ∀ x, x ∈ S ↔ -x ∈ S

/-- A pointed ordinary Cayley-graph isomorphism on the common carrier. -/
def pointedCayleyGraphIso {r : ℕ}
    (S T : Set (CayleyCarrier r))
    (f : CayleyCarrier r ≃ CayleyCarrier r) : Prop :=
  f 0 = 0 ∧
    ∀ x y, y - x ∈ S ↔ f y - f x ∈ T

/-- Preservation of the standard cyclic-nine fibre partition. -/
def preservesStandardFibres {r : ℕ}
    (f : CayleyCarrier r ≃ CayleyCarrier r) : Prop :=
  ∃ β : Equiv.Perm (BinarySpace r),
    ∃ σ : BinarySpace r → Equiv.Perm C9,
      ∀ x z, f (x, z) = (β x, σ x z)

/-- The nonflexible source directions and their binary span. -/
def nonFlexibleDirections {r : ℕ}
    (S : Set (CayleyCarrier r)) : Set (BinarySpace r) :=
  {v | v ≠ 0 ∧ ¬ flexibleSection (sectionSet S v)}

def rigidSpan {r : ℕ} (S : Set (CayleyCarrier r)) :
    Submodule (ZMod 2) (BinarySpace r) :=
  Submodule.span (ZMod 2) (nonFlexibleDirections S)

/-- The exact fibre-preserving conclusion, including the proper-span
reduction and the full-span group-automorphism transport. -/
def fibrePreservingRigidConclusion {r : ℕ}
    (S T : Set (CayleyCarrier r))
    (f : CayleyCarrier r ≃ CayleyCarrier r) : Prop :=
  ∃ β : Equiv.Perm (BinarySpace r),
    ∃ σ : BinarySpace r → Equiv.Perm C9,
      (∀ x z, f (x, z) = (β x, σ x z)) ∧
      ∃ m : BinarySpace r → C9ˣ,
        ∃ c : BinarySpace r → C9,
          (∀ x z, σ x z = (m x : C9) * z + c x) ∧
          (∀ x y, x - y ∈ rigidSpan S → m x = m y) ∧
          (∀ v, v ∉ rigidSpan S →
            flexibleSection (sectionSet S v)) ∧
          (rigidSpan S = ⊤ →
            ∃ L : BinarySpace r ≃ₗ[ZMod 2] BinarySpace r,
              ∃ u : C9ˣ,
                ∃ e : CayleyCarrier r ≃+ CayleyCarrier r,
                  (∀ x,
                    e x = (L x.1, (u : C9) * x.2)) ∧
                  e '' S = T)

/-- Claim 61234: exact cyclic-nine bipartite rigidity and the corrected
fibre-preserving theorem for binary ranks three through five. -/
def claim61234 : Prop :=
  cyclicNineBipartiteRigidity ∧
    ∀ r : ℕ, (r = 3 ∨ r = 4 ∨ r = 5) →
      ∀ S T : Set (CayleyCarrier r),
        identityFree S → identityFree T →
        inverseClosed S → inverseClosed T →
        ∀ f : CayleyCarrier r ≃ CayleyCarrier r,
          pointedCayleyGraphIso S T f →
          preservesStandardFibres f →
          rigidSpan S ≠ (⊥ : Submodule (ZMod 2) (BinarySpace r)) →
          fibrePreservingRigidConclusion S T f

end

end MathlibPlus.Open.ResearchFormalization.Claim61234
