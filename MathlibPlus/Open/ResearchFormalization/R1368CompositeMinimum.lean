import MathlibPlus.Open.Research.R1468

namespace MathlibPlus.Open.ResearchFormalization.R1368CompositeMinimum

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

abbrev binaryPair1368 := ZMod 2 × ZMod 2
abbrev ternaryPair1368 := ZMod 3 × ZMod 3
abbrev componentVertex1368 := binaryPair1368 × ternaryPair1368
abbrev outerVertex1368 := ZMod 2 × componentVertex1368

def binaryE1_1368 : binaryPair1368 := (1, 0)
def binaryE2_1368 : binaryPair1368 := (0, 1)
def binaryE12_1368 : binaryPair1368 := binaryE1_1368 + binaryE2_1368

def componentAdj1368
    (x y : componentVertex1368) : Prop :=
  (x.1 = y.1 ∧ x.2 ≠ y.2) ∨
    (x.1 - y.1 = binaryE1_1368 ∧ x.2.2 = y.2.2) ∨
    (x.1 - y.1 = binaryE2_1368 ∧ x.2.1 = y.2.1)

def outerAdj1368 (x y : outerVertex1368) : Prop :=
  x.1 = y.1 ∧ componentAdj1368 x.2 y.2

def componentFiber1368 (v : binaryPair1368) : Set componentVertex1368 :=
  {x | x.1 = v}

def componentVerticalLine1368 (h k : ternaryPair1368) : Prop :=
  h.2 = k.2

def componentHorizontalLine1368 (h k : ternaryPair1368) : Prop :=
  h.1 = k.1

/-- The unique composite-minimum graph type and its explicitly tied
valency-fourteen representative. -/
def soleCompositeRow1368 : Prop :=
  Set.ncard {q : GraphType1368 |
      q ∈ nonnormalRows ∧ 3 < rowMinimumBlockSize1368 q} = 1 ∧
    ∃ S : Connection14,
      nonnormalRow S ∧
      Quotient.mk (graphSetoid 14) S ∈ nonnormalRows ∧
      rowMinimumBlockSize1368 (Quotient.mk (graphSetoid 14) S) = 9 ∧
      minimumInvariantBlockSize1368 S = 9 ∧
      ∃ e : G1368 ≃ outerVertex1368, ∀ x y : G1368,
        cayleyAdj S.1 x y ↔
          outerAdj1368 (e x) (e y)

/-- Claim 38291: the sole composite-minimum row is the displayed two-copy
outer graph, whose component has four C₃² fibres, the two line relations,
and no diagonal quotient edges. -/
def claim38291_soleCompositeComponent : Prop :=
  soleCompositeRow1368 ∧
    Fintype.card componentVertex1368 = 36 ∧
    (∀ x : componentVertex1368,
      Set.ncard {y | componentAdj1368 x y} = 14) ∧
    (∀ v : binaryPair1368, ∀ h k : ternaryPair1368,
      h ≠ k → componentAdj1368 (v, h) (v, k)) ∧
    (∀ v : binaryPair1368, ∀ h k : ternaryPair1368,
      componentAdj1368 (v, h) (v + binaryE1_1368, k) ↔
        componentVerticalLine1368 h k) ∧
    (∀ v : binaryPair1368, ∀ h k : ternaryPair1368,
      componentAdj1368 (v, h) (v + binaryE2_1368, k) ↔
        componentHorizontalLine1368 h k) ∧
    (∀ v : binaryPair1368, ∀ h k : ternaryPair1368,
      ¬ componentAdj1368 (v, h) (v + binaryE12_1368, k)) ∧
    (∀ x y : componentVertex1368,
      Relation.ReflTransGen componentAdj1368 x y) ∧
    (∀ z z' : ZMod 2, ∀ x y : componentVertex1368,
      outerAdj1368 (z, x) (z', y) ↔
        (z = z' ∧ componentAdj1368 x y))

end

end MathlibPlus.Open.ResearchFormalization.R1368CompositeMinimum
