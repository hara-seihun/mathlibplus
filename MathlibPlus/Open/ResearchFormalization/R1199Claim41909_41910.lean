import MathlibPlus.Open.ResearchFormalization.R1199Claim32137
import MathlibPlus.Open.ResearchFormalization.R1199TargetFaithfulness

namespace MathlibPlus.Open.ResearchFormalization.R1199RepairedCensus

noncomputable section

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

private def fullGroupNonnormal (S : ConnectionSet) : Prop :=
  naturalRegularCopy ⊆ fullGraphGroup S ∧
    ¬ (∀ p, p ∈ fullGraphGroup S →
      ∀ t, t ∈ naturalRegularCopy → p * t * p⁻¹ ∈ naturalRegularCopy)

private def classifiedRows : Set (Set (Equiv.Perm G)) :=
  {H | ∃ S : ConnectionSet,
    fullGroupNonnormal S ∧ H = fullGraphGroup S}

private def rowIntrinsicCosetSystem
    (H : Set (Equiv.Perm G)) (K : AddSubgroup G) : Prop :=
  1 < Set.ncard (K : Set G) ∧
    Set.ncard (K : Set G) < Fintype.card G ∧
      ∀ p, p ∈ H → ∀ x y : G,
        y - x ∈ K ↔ p y - p x ∈ K

private def rowMinimumIntrinsicCosetSystem
    (H : Set (Equiv.Perm G)) (K : AddSubgroup G) : Prop :=
  rowIntrinsicCosetSystem H K ∧
    ∀ L : AddSubgroup G,
      rowIntrinsicCosetSystem H L →
        Set.ncard (K : Set G) ≤ Set.ncard (L : Set G)

private def minimumBlockSize (H : Set (Equiv.Perm G)) : ℕ :=
  sInf {n : ℕ | ∃ K : AddSubgroup G,
    rowMinimumIntrinsicCosetSystem H K ∧ Set.ncard (K : Set G) = n}

private def rowHasMinimumBlockSize
    (H : Set (Equiv.Perm G)) (n : ℕ) : Prop :=
  H ∈ classifiedRows ∧ minimumBlockSize H = n

private def twoPointRows : Set (Set (Equiv.Perm G)) :=
  {H | rowHasMinimumBlockSize H 2}

private def threePointRows : Set (Set (Equiv.Perm G)) :=
  {H | rowHasMinimumBlockSize H 3}

private def largerRows : Set (Set (Equiv.Perm G)) :=
  {H | H ∈ classifiedRows ∧ 3 < minimumBlockSize H}

private def literalTwoPointSystems :
    Set (Set (Equiv.Perm G) × AddSubgroup G) :=
  {z | z.1 ∈ twoPointRows ∧
    rowMinimumIntrinsicCosetSystem z.1 z.2 ∧
      Set.ncard (z.2 : Set G) = 2}

private def preservesCosets
    (H : Set (Equiv.Perm G)) (K : AddSubgroup G) : Prop :=
  ∀ p, p ∈ H → ∀ x y : G,
    y - x ∈ K ↔ p y - p x ∈ K

private def actualInducedQuotientImage
    (H : Set (Equiv.Perm G)) (K : AddSubgroup G) :
    Set (Equiv.Perm (G ⧸ K)) :=
  {q | ∃ p : Equiv.Perm G,
    p ∈ H ∧ preservesCosets H K ∧
      ∀ x : G,
        q (QuotientAddGroup.mk (s := K) x) =
          QuotientAddGroup.mk (s := K) (p x)}

private def naturalQuotientCopy (K : AddSubgroup G) :
    Set (Equiv.Perm (G ⧸ K)) :=
  {q | ∃ t : G, ∀ x : G,
    q (QuotientAddGroup.mk (s := K) x) =
      QuotientAddGroup.mk (s := K) (x + t)}

private abbrev QuotientGroupRecord :=
  Σ K : AddSubgroup G, Set (Equiv.Perm (G ⧸ K))

private abbrev QuotientPairRecord :=
  Σ K : AddSubgroup G,
    Set (Equiv.Perm (G ⧸ K)) × Set (Equiv.Perm (G ⧸ K))

private def quotientPairFor
    (z : Set (Equiv.Perm G) × AddSubgroup G) : QuotientPairRecord :=
  ⟨z.2, (actualInducedQuotientImage z.1 z.2,
    naturalQuotientCopy z.2)⟩

private def quotientGroupFor
    (z : Set (Equiv.Perm G) × AddSubgroup G) : QuotientGroupRecord :=
  ⟨z.2, actualInducedQuotientImage z.1 z.2⟩

private def quotientPairRecords : Set QuotientPairRecord :=
  {q | ∃ z : Set (Equiv.Perm G) × AddSubgroup G,
    z ∈ literalTwoPointSystems ∧ q = quotientPairFor z}

private def quotientGroupRecords : Set QuotientGroupRecord :=
  {q | ∃ z : Set (Equiv.Perm G) × AddSubgroup G,
    z ∈ literalTwoPointSystems ∧ q = quotientGroupFor z}

/-- Claim 41909: the exact classified full-group row carrier has the
2041-row minimum-system trichotomy. -/
def exhaustiveMinimumSystemTrichotomy_claim41909 : Prop :=
  Set.ncard classifiedRows = 2041 ∧
    Set.ncard twoPointRows = 1977 ∧
      Set.ncard threePointRows = 51 ∧
        Set.ncard largerRows = 13 ∧
          Disjoint twoPointRows threePointRows ∧
            Disjoint twoPointRows largerRows ∧
              Disjoint threePointRows largerRows ∧
                classifiedRows = twoPointRows ∪ threePointRows ∪ largerRows

/-- Claim 41910: two-point systems are first literal `(full-group image,
minimum intrinsic subgroup)` records; only afterward are actual quotient
images paired with the natural quotient copy and deduplicated. -/
def twoPointBranchCensus_claim41910 : Prop :=
  Set.ncard twoPointRows = 1977 ∧
    Set.ncard literalTwoPointSystems = 6209 ∧
      (∀ z : Set (Equiv.Perm G) × AddSubgroup G,
        z ∈ literalTwoPointSystems →
          Nat.card (G ⧸ z.2) = 36) ∧
        Set.ncard quotientPairRecords = 738 ∧
          Set.ncard quotientGroupRecords = 668

end

end MathlibPlus.Open.ResearchFormalization.R1199RepairedCensus
