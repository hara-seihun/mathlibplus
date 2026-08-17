import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1199TargetFaithfulness

private abbrev C2Part := Fin 3 → ZMod 2
private abbrev C3Part := Fin 2 → ZMod 3
private abbrev G := C2Part × C3Part

private abbrev ConnectionSet :=
  {S : Finset G //
    0 ∉ S ∧
      (∀ x : G, x ∈ S ↔ -x ∈ S) ∧
      (S.card = 11 ∨ S.card = 12)}

private def cayleyAdj (S : ConnectionSet) (x y : G) : Prop :=
  x ≠ y ∧ y - x ∈ S.1

private def fullGraphGroup (S : ConnectionSet) : Set (Equiv.Perm G) :=
  {p | ∀ x y : G,
    cayleyAdj S x y ↔ cayleyAdj S (p x) (p y)}

private def naturalRegularCopy : Set (Equiv.Perm G) :=
  Set.range (fun a : G => Equiv.addRight a)

private def isPermutationSubgroup (H : Set (Equiv.Perm G)) : Prop :=
  1 ∈ H ∧
    (∀ p q, p ∈ H → q ∈ H → p * q ∈ H) ∧
      ∀ p, p ∈ H → p⁻¹ ∈ H

private def isRegularCopy (H : Set (Equiv.Perm G)) : Prop :=
  isPermutationSubgroup H ∧
    ∃ ρ : G → Equiv.Perm G,
      Function.Injective ρ ∧
        (∀ a b : G, ρ (a + b) = ρ a * ρ b) ∧
          Set.range ρ = H ∧
            ∀ x y : G, ∃! a : G, ρ a x = y

private def preservesCosets (H : Set (Equiv.Perm G)) (K : AddSubgroup G) : Prop :=
  ∀ p, p ∈ H → ∀ x y : G,
    y - x ∈ K ↔ p y - p x ∈ K

private def actualInducedQuotientImage
    (S : ConnectionSet) (K : AddSubgroup G) :
    Set (Equiv.Perm (G ⧸ K)) :=
  {q | ∃ p : Equiv.Perm G,
    p ∈ fullGraphGroup S ∧
      (∀ x y : G, y - x ∈ K ↔ p y - p x ∈ K) ∧
        ∀ x : G,
          q (QuotientAddGroup.mk (s := K) x) =
            QuotientAddGroup.mk (s := K) (p x)}

private def arisesInQuotientLift
    (S : ConnectionSet) (K : AddSubgroup G)
    (H : Set (Equiv.Perm G)) : Prop :=
  H ⊆ fullGraphGroup S ∧
    isRegularCopy H ∧
      preservesCosets H K ∧
        ∀ p, p ∈ H →
          ∃ q : Equiv.Perm (G ⧸ K),
            q ∈ actualInducedQuotientImage S K ∧
              ∀ x : G,
                q (QuotientAddGroup.mk (s := K) x) =
                  QuotientAddGroup.mk (s := K) (p x)

private def fullGroupNonnormal (S : ConnectionSet) : Prop :=
  naturalRegularCopy ⊆ fullGraphGroup S ∧
    ¬ (∀ p, p ∈ fullGraphGroup S →
        ∀ t, t ∈ naturalRegularCopy → p * t * p⁻¹ ∈ naturalRegularCopy)

private def intrinsicCosetSystem
    (S : ConnectionSet) (K : AddSubgroup G) : Prop :=
  1 < Set.ncard (K : Set G) ∧
    Set.ncard (K : Set G) < Fintype.card G ∧
      ∀ p, p ∈ fullGraphGroup S → ∀ x y : G,
        y - x ∈ K ↔ p y - p x ∈ K

private def minimumIntrinsicCosetSystem
    (S : ConnectionSet) (K : AddSubgroup G) : Prop :=
  intrinsicCosetSystem S K ∧
    ∀ L : AddSubgroup G,
      intrinsicCosetSystem S L →
        Set.ncard (K : Set G) ≤ Set.ncard (L : Set G)

private def conjugateToNatural
    (S : ConnectionSet) (H : Set (Equiv.Perm G)) : Prop :=
  ∃ a : Equiv.Perm G,
    a ∈ fullGraphGroup S ∧
      ∀ p, p ∈ H ↔ a * p * a⁻¹ ∈ naturalRegularCopy

/-- Claim 41922: every regular copy in every minimum intrinsic-system
branch on the exact valency-eleven/twelve nonnormal boundary is conjugate to
natural translation.  The route condition is precisely preservation of the
minimum subgroup-coset system, so no 2-closure hypothesis is imposed. -/
def claim41922_completeLowBoundaryTargetFaithfulness : Prop :=
  ∀ S : ConnectionSet,
    fullGroupNonnormal S →
      ∀ K : AddSubgroup G,
        minimumIntrinsicCosetSystem S K →
          ∀ H : Set (Equiv.Perm G),
            arisesInQuotientLift S K H →
              conjugateToNatural S H

end MathlibPlus.Open.ResearchFormalization.R1199TargetFaithfulness
