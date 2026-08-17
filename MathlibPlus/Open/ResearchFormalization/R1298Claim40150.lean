import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1298Claim40150

noncomputable section

abbrev LocalVector := Fin 3 → ZMod 2
abbrev LocalPermutation := Equiv.Perm LocalVector

def isCanonicalChart (c : LocalPermutation) : Prop :=
  c = 1 ∨
    ∃ a b : LocalVector,
      a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ c = Equiv.swap a b

abbrev CanonicalChart := {c : LocalPermutation // isCanonicalChart c}

/-- The normalized block map on a finite direct factor. -/
def normalizedBlockMap {B : Type*}
    (c : B → CanonicalChart) : LocalVector × B → LocalVector × B :=
  fun x => ((c x.2 : LocalPermutation) x.1, x.2)

/-- The exact normalized relative-derivative action supplied by Record 6. -/
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

def relativeDerivativeOrbit {B : Type*} [Group B]
    (c : B → CanonicalChart) (x : LocalVector × B) :
    Set (LocalVector × B) :=
  {y | ∃ h : fullRelativeDerivativeGroup c,
    (h : Equiv.Perm (LocalVector × B)) x = y}

/-- Claim 40150: every canonical chart profile on every finite direct factor
fixes every orbit of its full normalized relative-derivative group. -/
def claim40150 : Prop :=
  ∀ (B : Type*) [Group B] [Fintype B]
    (c : B → CanonicalChart),
    ∀ x : LocalVector × B,
      Set.image (normalizedBlockMap c) (relativeDerivativeOrbit c x) =
        relativeDerivativeOrbit c x

end

end MathlibPlus.Open.ResearchFormalization.R1298Claim40150
