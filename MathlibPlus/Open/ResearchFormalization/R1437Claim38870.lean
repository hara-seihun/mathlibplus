import MathlibPlus.Open.ResearchFormalization.R1437.Claim38865

namespace MathlibPlus.Open.ResearchFormalization.R1437Claim38870

open MathlibPlus.Open.ResearchFormalizationBatch_01a0014d

noncomputable section

abbrev H := C6Squared
abbrev OuterPoints := H × Bool
abbrev SixSymmetric := Equiv.Perm (Fin 6)

/-- A cyclic subgroup of order six in `C₆²`. -/
def cyclicOrderSixSubgroup38870 (K : AddSubgroup H) : Prop :=
  Nonempty (K ≃+ ZMod 6)

/-- An unordered pair of complementary cyclic order-six factors. -/
def unorderedCyclicDirectFactorDecomposition38870
    (P : Finset (AddSubgroup H)) : Prop :=
  P.card = 2 ∧
    (∀ K ∈ P, cyclicOrderSixSubgroup38870 K) ∧
    ∃ K L : AddSubgroup H,
      K ∈ P ∧ L ∈ P ∧ K ≠ L ∧
        K ⊔ L = ⊤ ∧ K ⊓ L = ⊥

/-- The orbit of a point under a permutation of six points. -/
def permutationOrbit38870 (σ : SixSymmetric) (x : Fin 6) : Set (Fin 6) :=
  {y | ∃ n : ℕ, (σ ^ n) x = y}

def isSixCycle38870 (σ : SixSymmetric) : Prop :=
  ∀ x : Fin 6, permutationOrbit38870 σ x = Set.univ

/-- Cycle type `3+2+1`, expressed by its three disjoint permutation orbits. -/
def isCycleType32138870 (σ : SixSymmetric) : Prop :=
  ∃ x y z : Fin 6,
    Set.ncard (permutationOrbit38870 σ x) = 3 ∧
      Set.ncard (permutationOrbit38870 σ y) = 2 ∧
        Set.ncard (permutationOrbit38870 σ z) = 1 ∧
          Disjoint (permutationOrbit38870 σ x)
            (permutationOrbit38870 σ y) ∧
          Disjoint (permutationOrbit38870 σ x)
            (permutationOrbit38870 σ z) ∧
          Disjoint (permutationOrbit38870 σ y)
            (permutationOrbit38870 σ z) ∧
          permutationOrbit38870 σ x ∪
              permutationOrbit38870 σ y ∪
              permutationOrbit38870 σ z = Set.univ

def innerGroupAutomorphism38870 {G : Type*} [Group G]
    (φ : G ≃* G) : Prop :=
  ∃ a : G, ∀ x : G, φ x = a⁻¹ * x * a

/-- The degree-six alternating simple factor. -/
def alternatingSix38870 : Subgroup (Equiv.Perm (ZMod 6)) :=
  Subgroup.closure
    {g : Equiv.Perm (ZMod 6) | Equiv.Perm.sign g = 1}

/-- The two-transitive degree-six `A₅` action is recorded by its actual
permutation subgroup, rather than by a guessed natural degree-five action. -/
def degreeSixA5Action38870
    (L : Subgroup (Equiv.Perm (ZMod 6))) : Prop :=
  Nat.card L = 60 ∧
    (∀ x y : ZMod 6, ∃ g : L,
      (g : Equiv.Perm (ZMod 6)) x = y) ∧
    (∀ x₁ x₂ y₁ y₂ : ZMod 6,
      x₁ ≠ x₂ → y₁ ≠ y₂ →
        ∃ g : L,
          (g : Equiv.Perm (ZMod 6)) x₁ = y₁ ∧
            (g : Equiv.Perm (ZMod 6)) x₂ = y₂)

def crossStripAction38870
    (L : Subgroup (Equiv.Perm (ZMod 6))) : Prop :=
  degreeSixA5Action38870 L ∨ L = alternatingSix38870

def coordinatePermutation38870 (g : Equiv.Perm (ZMod 6))
    (coordinate : Bool) : Equiv.Perm H :=
  if coordinate then
    Equiv.prodCongr (Equiv.refl (ZMod 6)) g
  else
    Equiv.prodCongr g (Equiv.refl (ZMod 6))

/-- A cross-block strip acts on opposite local coordinates in the two outer
blocks. -/
def crossStripElement38870 (g : Equiv.Perm (ZMod 6))
    (coordinate : Bool) : Equiv.Perm OuterPoints :=
  if coordinate then
    blockwisePermutation
      (coordinatePermutation38870 g false)
      (coordinatePermutation38870 g true)
  else
    blockwisePermutation
      (coordinatePermutation38870 g true)
      (coordinatePermutation38870 g false)

def crossStripKernel38870
    (L : Subgroup (Equiv.Perm (ZMod 6))) :
    Subgroup (Equiv.Perm OuterPoints) :=
  Subgroup.closure
    {f | ∃ g : Equiv.Perm (ZMod 6), g ∈ L ∧
      (f = crossStripElement38870 g false ∨
        f = crossStripElement38870 g true)}

def crossStripModel38870
    (L : Subgroup (Equiv.Perm (ZMod 6))) :
    Subgroup (Equiv.Perm OuterPoints) :=
  Subgroup.closure
    ((crossStripKernel38870 L : Set (Equiv.Perm OuterPoints)) ∪
      ({unshiftedBlockSwap} : Set (Equiv.Perm OuterPoints)))

def crossStripNormalizes38870
    (L : Subgroup (Equiv.Perm (ZMod 6))) (a : H) : Prop :=
  complementShift a ∈
    Subgroup.normalizer (crossStripModel38870 L : Set (Equiv.Perm OuterPoints))

def twoTorsion38870 (a : H) : Prop :=
  a + a = 0

def generatedRegularGroup38870 (a : H) :
    Subgroup (Equiv.Perm OuterPoints) :=
  Subgroup.closure
    ((Set.range (blockAction : H → Equiv.Perm OuterPoints)) ∪
      ({complementShift a} : Set (Equiv.Perm OuterPoints)))

/-- Claim 38870: the exact `C₆²` automorphism/direct-factor census, the
exceptional `S₆` six-cycle calculation, and the cross-strip normalizer
boundary. -/
def claim38870 : Prop :=
  Fintype.card H = 36 ∧
    Nat.card (H ≃+ H) = 288 ∧
    Nat.card {K : AddSubgroup H //
      cyclicOrderSixSubgroup38870 K} = 12 ∧
    Nat.card {P : Finset (AddSubgroup H) //
      unorderedCyclicDirectFactorDecomposition38870 P} = 36 ∧
    Nat.card {σ : SixSymmetric // isSixCycle38870 σ} = 120 ∧
    (∃ φ : SixSymmetric ≃* SixSymmetric,
      ¬ innerGroupAutomorphism38870 φ ∧
        ∀ σ : SixSymmetric,
          isSixCycle38870 σ → isCycleType32138870 (φ σ)) ∧
    (∀ L : Subgroup (Equiv.Perm (ZMod 6)),
      crossStripAction38870 L →
        Nat.card {a : H // crossStripNormalizes38870 L a} = 4 ∧
          (∀ a : H,
            crossStripNormalizes38870 L a ↔ twoTorsion38870 a) ∧
          (∀ a : H, addOrderOf a = 3 →
            ¬ crossStripNormalizes38870 L a) ∧
          (∀ a : H, twoTorsion38870 a →
            generatedRegularGroup38870 a =
              generatedRegularGroup38870 0))

end

end MathlibPlus.Open.ResearchFormalization.R1437Claim38870
