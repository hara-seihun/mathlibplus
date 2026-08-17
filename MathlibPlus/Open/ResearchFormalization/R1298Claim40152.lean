import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1298Claim40152

noncomputable section

abbrev LocalVector := Fin 3 → ZMod 2
abbrev LocalPermutation := Equiv.Perm LocalVector
abbrev SectionFactor := Multiplicative (ZMod 2) × Multiplicative (ZMod 9)
abbrev Ambient := LocalVector × SectionFactor

def isCanonicalChart (c : LocalPermutation) : Prop :=
  c = 1 ∨
    ∃ a b : LocalVector,
      a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ c = Equiv.swap a b

abbrev CanonicalChart := {c : LocalPermutation // isCanonicalChart c}

def normalizedBlockMap {B : Type*}
    (c : B → CanonicalChart) : LocalVector × B → LocalVector × B :=
  fun x => ((c x.2 : LocalPermutation) x.1, x.2)

def normalizedRelativeDerivativeSet {B : Type*} [Group B]
    (c : B → CanonicalChart) :
    Set (Equiv.Perm (LocalVector × B)) :=
  {d | ∃ a : LocalVector, ∃ s : B,
    ∀ v : LocalVector, ∀ b : B,
      d (v, b) =
        (((c b : LocalPermutation)⁻¹)
          ((c s : LocalPermutation) a +
            (c (b * s) : LocalPermutation) (v + a)), b)}

def fullRelativeDerivativeGroup {B : Type*} [Group B]
    (c : B → CanonicalChart) :
    Subgroup (Equiv.Perm (LocalVector × B)) :=
  Subgroup.closure (normalizedRelativeDerivativeSet c)

def invariantUnderRelativeDerivatives {B : Type*} [Group B]
    (c : B → CanonicalChart) (S : Set (LocalVector × B)) : Prop :=
  ∀ h : fullRelativeDerivativeGroup c,
    Set.image (h : Equiv.Perm (LocalVector × B)) S = S

def ambientInverse (x : LocalVector × SectionFactor) :
    LocalVector × SectionFactor :=
  (-x.1, x.2⁻¹)

def inverseClosed (S : Set Ambient) : Prop :=
  ∀ x : Ambient, x ∈ S ↔ ambientInverse x ∈ S

def recordEightClosure (c : SectionFactor → CanonicalChart) : Prop :=
  (∀ S : Set Ambient,
    invariantUnderRelativeDerivatives c S →
      Set.image (normalizedBlockMap c) S = S) ∧
    (∀ S : Set Ambient,
      inverseClosed S →
        invariantUnderRelativeDerivatives c S →
          Set.image (normalizedBlockMap c) S = S)

/-- Claim 40152: on the 18-section factor `C₂ × C₉`, all `22^18` canonical
profiles on the degree-eight fibre close both directed and inverse-closed
connection sets. -/
def claim40152 : Prop :=
  Fintype.card SectionFactor = 18 ∧
    Fintype.card LocalVector = 8 ∧
      Fintype.card Ambient = 144 ∧
        Nat.card (SectionFactor → CanonicalChart) = 22 ^ 18 ∧
          ∀ c : SectionFactor → CanonicalChart,
            recordEightClosure c

end

end MathlibPlus.Open.ResearchFormalization.R1298Claim40152
