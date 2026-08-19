import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.ResearchFormalize39607

private abbrev C2Part := Fin 3 → ZMod 2
private abbrev C3Part := Fin 2 → ZMod 3
private abbrev Carrier := C2Part × C3Part

private def ordinaryConnection (S : Set Carrier) : Prop :=
  (0 : Carrier) ∉ S ∧ ∀ x : Carrier, x ∈ S ↔ -x ∈ S

private def cayleyAdj (S : Set Carrier) (x y : Carrier) : Prop :=
  x ≠ y ∧ y - x ∈ S

private def fullGraphGroup (S : Set Carrier) : Set (Equiv.Perm Carrier) :=
  {p | ∀ x y : Carrier,
    cayleyAdj S x y ↔ cayleyAdj S (p x) (p y)}

private def additiveCoset (K : AddSubgroup Carrier) (x : Carrier) : Set Carrier :=
  {y | y - x ∈ K}

private def cosetPartition (K : AddSubgroup Carrier) : Set (Set Carrier) :=
  {C | ∃ x : Carrier, C = additiveCoset K x}

private def preservesCosetPartition
    (S : Set Carrier) (K : AddSubgroup Carrier) : Prop :=
  ∀ p, p ∈ fullGraphGroup S →
    ∀ C, C ∈ cosetPartition K →
      ∃ D, D ∈ cosetPartition K ∧ Set.image p C = D

private def intrinsicCosetSystem
    (S : Set Carrier) (K : AddSubgroup Carrier) : Prop :=
  1 < Set.ncard (K : Set Carrier) ∧
    Set.ncard (K : Set Carrier) < Fintype.card Carrier ∧
      preservesCosetPartition S K ∧
        ∀ p, p ∈ fullGraphGroup S → ∀ x y : Carrier,
          y - x ∈ K ↔ p y - p x ∈ K

private def minimumIntrinsicCosetSystem
    (S : Set Carrier) (K : AddSubgroup Carrier) : Prop :=
  intrinsicCosetSystem S K ∧
    ∀ L : AddSubgroup Carrier,
      intrinsicCosetSystem S L →
        Set.ncard (K : Set Carrier) ≤ Set.ncard (L : Set Carrier)

/-- Claim 39607: the proper nontrivial divisors of the fixed order-72
carrier are exactly the ten displayed minimum block sizes, and every
intrinsic minimum subgroup-coset system for an ordinary inverse-closed
identity-free Cayley connection set has one of those block sizes. -/
def claim39607_exact_minimum_block_sizes : Prop :=
  Fintype.card Carrier = 72 ∧
    ({d : ℕ | d ∣ 72 ∧ 1 < d ∧ d < 72} : Set ℕ) =
      ({2, 3, 4, 6, 8, 9, 12, 18, 24, 36} : Set ℕ) ∧
    ∀ (S : Set Carrier),
      ordinaryConnection S →
        ∀ K : AddSubgroup Carrier,
          minimumIntrinsicCosetSystem S K →
            Set.ncard (K : Set Carrier) ∈
              ({2, 3, 4, 6, 8, 9, 12, 18, 24, 36} : Set ℕ)

end MathlibPlus.Open.ResearchFormalization.ResearchFormalize39607
