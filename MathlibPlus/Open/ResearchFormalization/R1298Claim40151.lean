import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1298Claim40151

noncomputable section

abbrev LocalVector := Fin 3 → ZMod 2
abbrev LocalPermutation := Equiv.Perm LocalVector
def isCanonicalChart (c : LocalPermutation) : Prop :=
  c = 1 ∨
    ∃ a b : LocalVector,
      a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ c = Equiv.swap a b

abbrev CanonicalChart := {c : LocalPermutation // isCanonicalChart c}

/-- The normalized block map on the direct product. -/
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

/-- Inversion in the direct product `C₂³ × B`. -/
def ambientInverse {B : Type*} [Group B]
    (x : LocalVector × B) : LocalVector × B :=
  (-x.1, x.2⁻¹)

def inverseClosed {B : Type*} [Group B]
    (S : Set (LocalVector × B)) : Prop :=
  ∀ x : LocalVector × B, x ∈ S ↔ ambientInverse x ∈ S

/-- Claim 40151: all directed invariant connection sets are fixed by the
canonical profile map, with the inverse-closed case included, so neither
kind of canonical profile can witness a Cayley-isomorphism failure. -/
def claim40151 : Prop :=
  ∀ (B : Type*) [Group B] [Fintype B]
    (c : B → CanonicalChart),
    (∀ S : Set (LocalVector × B),
      invariantUnderRelativeDerivatives c S →
        Set.image (normalizedBlockMap c) S = S) ∧
      (∀ S : Set (LocalVector × B),
        inverseClosed S →
          invariantUnderRelativeDerivatives c S →
            Set.image (normalizedBlockMap c) S = S) ∧
        (¬∃ S : Set (LocalVector × B),
          invariantUnderRelativeDerivatives c S ∧
            Set.image (normalizedBlockMap c) S ≠ S) ∧
          (¬∃ S : Set (LocalVector × B),
            inverseClosed S ∧
              invariantUnderRelativeDerivatives c S ∧
                Set.image (normalizedBlockMap c) S ≠ S)

end

end MathlibPlus.Open.ResearchFormalization.R1298Claim40151
