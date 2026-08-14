import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBlocks

/-- The regular fibre group D ≅ C₃² used by the block-action claims. -/
abbrev Fibre := ZMod 3 × ZMod 3

/-- Coordinates for a point in a block system with fibre D. -/
abbrev BlockVertex (β : Type*) := Fibre × β

/-- Translation by a fibre element on every block. -/
def fibreTranslation {β : Type*} (a : Fibre) : Equiv.Perm (BlockVertex β) :=
  { toFun := fun z => (z.1 + a, z.2)
    invFun := fun z => (z.1 - a, z.2)
    left_inv := by
      intro z
      rcases z with ⟨d, b⟩
      simp [sub_eq_add_neg, add_assoc]
    right_inv := by
      intro z
      rcases z with ⟨d, b⟩
      simp [sub_eq_add_neg, add_assoc] }

/-- The regular fibre translations are present in the block action. -/
def regularFibreTranslations {β : Type*}
    (H : Subgroup (Equiv.Perm (BlockVertex β))) : Prop :=
  ∀ a : Fibre, fibreTranslation a ∈ H

/-- H carries each fibre block onto a fibre block. -/
def blockSystemInvariant {β : Type*}
    (H : Subgroup (Equiv.Perm (BlockVertex β))) : Prop :=
  ∀ h : H, ∀ b : β, ∃ c : β, ∀ d : Fibre,
    ((h : Equiv.Perm (BlockVertex β)) (d, b)).2 = c

/-- Two ordered pairs lie in the same H-orbital. -/
def sameHOrbital {β : Type*}
    (H : Subgroup (Equiv.Perm (BlockVertex β)))
    (p q : (BlockVertex β) × (BlockVertex β)) : Prop :=
  ∃ h : H,
    ((h : Equiv.Perm (BlockVertex β)) p.1,
      (h : Equiv.Perm (BlockVertex β)) p.2) = q

/-- The allowed-shift space from block b to block c. -/
def allowedShiftSpace {β : Type*}
    (H : Subgroup (Equiv.Perm (BlockVertex β)))
    (b c : β) : Set Fibre :=
  {a | ∀ x : Fibre,
    sameHOrbital H ((0, b), (x, c)) ((0, b), (x + a, c))}

/-- Claim 6532: all off-diagonal allowed-shift spaces are D. -/
def offDiagonalSaturation {β : Type*} [Fintype β]
    (H : Subgroup (Equiv.Perm (BlockVertex β)))
    (_hInvariant : blockSystemInvariant H)
    (_hRegular : regularFibreTranslations H) : Prop :=
  ∀ b c : β, b ≠ c → allowedShiftSpace H b c = Set.univ

end MathlibPlus.Open.ResearchFormalizationBlocks
