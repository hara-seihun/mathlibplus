import MathlibPlus.Open.Research.R1468

namespace MathlibPlus.Open.ResearchFormalization.R1368Valency14Histogram

noncomputable section

open MathlibPlus.Open.Research.R1468

abbrev G1368 := CayleyGroup
abbrev Connection14 := ConnectionSet 14
abbrev GraphType1368 := Quotient (graphSetoid 14)

def graphAutomorphismSet (S : Connection14) : Set (Equiv.Perm G1368) :=
  {e | preservesGraph S e}

def naturalTranslationSubgroup : Subgroup (Equiv.Perm G1368) :=
  Subgroup.closure (Set.range translation)

def graphTranslationNormal (S : Connection14) : Prop :=
  ∀ e : Equiv.Perm G1368, e ∈ graphAutomorphismSet S →
    ∀ t : naturalTranslationSubgroup,
      e * (t : Equiv.Perm G1368) * e⁻¹ ∈ naturalTranslationSubgroup

def nonnormalRow (S : Connection14) : Prop :=
  ¬ graphTranslationNormal S

def graphTypeHas (P : Connection14 → Prop) (q : GraphType1368) : Prop :=
  ∃ S : Connection14, P S ∧ Quotient.mk (graphSetoid 14) S = q

def nonnormalRows : Set GraphType1368 :=
  {q | graphTypeHas nonnormalRow q}

def connectedCayley1368 (S : Connection14) : Prop :=
  ∀ x y : G1368,
    Relation.ReflTransGen (cayleyAdj S.1) x y

def connectedNonnormalRows : Set GraphType1368 :=
  {q | graphTypeHas
    (fun S => nonnormalRow S ∧ connectedCayley1368 S) q}

def coset1368 (H : AddSubgroup G1368) (g : G1368) : Set G1368 :=
  {x | x - g ∈ H}

def properNontrivialSubgroup1368 (H : AddSubgroup G1368) : Prop :=
  H ≠ ⊥ ∧ H ≠ ⊤

def invariantCosetSystem1368
    (S : Connection14) (H : AddSubgroup G1368) : Prop :=
  properNontrivialSubgroup1368 H ∧
    ∀ e : Equiv.Perm G1368, e ∈ graphAutomorphismSet S →
      ∀ g : G1368, ∃ g' : G1368,
        Set.image e (coset1368 H g) = coset1368 H g'

def invariantCosetSystems1368 (S : Connection14) : Set (AddSubgroup G1368) :=
  {H | invariantCosetSystem1368 S H}

def minimumInvariantBlockSize1368 (S : Connection14) : Nat :=
  sInf {n : Nat | ∃ H : AddSubgroup G1368,
    H ∈ invariantCosetSystems1368 S ∧ n = Nat.card H}

def rowMinimumBlockSize1368 (q : GraphType1368) : Nat :=
  sInf {n : Nat | ∃ S : Connection14,
    Quotient.mk (graphSetoid 14) S = q ∧ nonnormalRow S ∧
      n = minimumInvariantBlockSize1368 S}

def rowsWithMinimum1368 (n : Nat) : Set GraphType1368 :=
  {q | q ∈ nonnormalRows ∧ rowMinimumBlockSize1368 q = n}

def connectedRowsWithMinimum1368 (n : Nat) : Set GraphType1368 :=
  {q | q ∈ connectedNonnormalRows ∧ rowMinimumBlockSize1368 q = n}

/-- Claim 38289: the exact minimum invariant subgroup-coset block
histogram, including its connected-row prime-size consequence. -/
def claim38289_minimumInvariantBlockHistogram : Prop :=
  Set.ncard nonnormalRows = 3043 ∧
    Set.ncard connectedNonnormalRows = 2596 ∧
    Set.ncard (rowsWithMinimum1368 2) = 2991 ∧
    Set.ncard (rowsWithMinimum1368 3) = 51 ∧
    Set.ncard (rowsWithMinimum1368 9) = 1 ∧
    Set.ncard (connectedRowsWithMinimum1368 2) = 2565 ∧
    Set.ncard (connectedRowsWithMinimum1368 3) = 31 ∧
    Set.ncard (connectedRowsWithMinimum1368 9) = 0 ∧
    (∀ q : GraphType1368, q ∈ connectedNonnormalRows →
      ∃ p : Nat, Nat.Prime p ∧ rowMinimumBlockSize1368 q = p)

end

end MathlibPlus.Open.ResearchFormalization.R1368Valency14Histogram
