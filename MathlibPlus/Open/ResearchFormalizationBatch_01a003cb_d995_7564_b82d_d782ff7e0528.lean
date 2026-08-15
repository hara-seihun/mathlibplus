import Mathlib

noncomputable section
open scoped BigOperators

universe u

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-! Claim 37006: degree filtration and profile-good members. -/

variable {α : Type*} [DecidableEq α]

def groundCoordinates (𝓕 : Finset (Finset α)) : Finset α :=
  𝓕.biUnion id

def coordinateDegree (𝓕 : Finset (Finset α)) (x : α) : ℕ :=
  (𝓕.filter (fun A => x ∈ A)).card

def degreeFiltration (𝓕 : Finset (Finset α)) (S j : ℕ) : Finset α :=
  (groundCoordinates 𝓕).filter (fun x => coordinateDegree 𝓕 x ≤ S ^ j)

def profileCount (𝓕 : Finset (Finset α)) (S j : ℕ) (A : Finset α) : ℕ :=
  (A ∩ degreeFiltration 𝓕 S j).card

def isKSunflower (k : ℕ) (𝓕 : Finset (Finset α)) : Prop :=
  ∃ 𝓑 : Finset (Finset α),
    𝓑 ⊆ 𝓕 ∧ 𝓑.card = k ∧
      ∃ K : Finset α,
        (∀ A ∈ 𝓑, K ⊆ A) ∧
          (∀ A ∈ 𝓑, ∀ B ∈ 𝓑, A ≠ B → A ∩ B = K)

def isDistinctUniformSunflowerFreeFamily
    (k r : ℕ) (𝓕 : Finset (Finset α)) : Prop :=
  (∀ A ∈ 𝓕, A.card = r) ∧ ¬ isKSunflower k 𝓕

def degreeFiltrationProfileContext
    (k S r : ℕ) (𝓕 : Finset (Finset α)) : Prop :=
  3 ≤ k ∧ 1 ≤ S ∧ isDistinctUniformSunflowerFreeFamily k r 𝓕

def profileGoodMember
    (𝓕 : Finset (Finset α)) (S r : ℕ) (A : Finset α) : Prop :=
  ∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ j ≤ profileCount 𝓕 S j A

def profileGoodFamily
    (𝓕 : Finset (Finset α)) (S r : ℕ) : Prop :=
  ∀ A ∈ 𝓕, profileGoodMember 𝓕 S r A

/-! Claims 37818--37819: the hyperplane--triad connection set. -/

abbrev BinaryVector (r : ℕ) := Fin r → ZMod 2
abbrev CyclicNine := ZMod 9
abbrev HyperplaneTriadGroup (r : ℕ) := BinaryVector r × CyclicNine

 def isBinaryHyperplane (r : ℕ)
    (U : Submodule (ZMod 2) (BinaryVector r)) : Prop :=
  U < (⊤ : Submodule (ZMod 2) (BinaryVector r)) ∧
    Module.finrank (ZMod 2) U = r - 1

def hyperplaneTriadConnectionSet (r : ℕ)
    (U : Submodule (ZMod 2) (BinaryVector r)) : Set (HyperplaneTriadGroup r) :=
  ({(0 : BinaryVector r)} ×ˢ (Set.univ \ {(0 : CyclicNine)})) ∪
    (((U : Set (BinaryVector r)) \ {0}) ×ˢ ({(3 : CyclicNine), (6 : CyclicNine)} : Set CyclicNine)) ∪
      ((Set.univ \ (U : Set (BinaryVector r))) ×ˢ {(0 : CyclicNine)})

def hyperplaneTriadCayleyGraph (r : ℕ)
    (U : Submodule (ZMod 2) (BinaryVector r)) :
    SimpleGraph (HyperplaneTriadGroup r) :=
  SimpleGraph.fromRel (fun x y =>
    -x + y ∈ hyperplaneTriadConnectionSet r U)

def isInverseClosedAdditive {A : Type*} [AddGroup A] (S : Set A) : Prop :=
  ∀ s, s ∈ S → -s ∈ S

def hyperplaneTriadConnectionClaim (r : ℕ)
    (U : Submodule (ZMod 2) (BinaryVector r)) : Prop :=
  3 ≤ r →
    isBinaryHyperplane r U →
      isInverseClosedAdditive (hyperplaneTriadConnectionSet r U) ∧
        AddSubgroup.closure (hyperplaneTriadConnectionSet r U) = ⊤ ∧
        ((0 : BinaryVector r), (1 : CyclicNine)) ∈
          hyperplaneTriadConnectionSet r U ∧
        Submodule.span (ZMod 2)
            (Set.univ \ (U : Set (BinaryVector r))) = ⊤ ∧
        (∃ e : BinaryVector r,
          e ∉ (U : Set (BinaryVector r)) ∧
            ∀ u : BinaryVector r, u ∈ (U : Set (BinaryVector r)) →
              e + u ∉ (U : Set (BinaryVector r)) ∧ e + (e + u) = u) ∧
        SimpleGraph.Connected (hyperplaneTriadCayleyGraph r U)

/-! Claim 37823: the hyperplane stabilizer has no nonzero fixed vector. -/

def hyperplaneStabilizer (r : ℕ)
    (U : Submodule (ZMod 2) (BinaryVector r)) :
    Set (BinaryVector r ≃ₗ[ZMod 2] BinaryVector r) :=
  {g | g '' (U : Set (BinaryVector r)) = (U : Set (BinaryVector r))}

def hyperplaneStabilizerNoNonzeroFixedVector (r : ℕ)
    (U : Submodule (ZMod 2) (BinaryVector r)) : Prop :=
  3 ≤ r → isBinaryHyperplane r U →
    ∀ v : BinaryVector r, v ≠ 0 →
      ∃ g : BinaryVector r ≃ₗ[ZMod 2] BinaryVector r,
        g ∈ hyperplaneStabilizer r U ∧ g v ≠ v

/-! Claim 37825: regular two-point blocks are subgroup cosets. -/

def twoPointBlockSystem {G : Type*} [Fintype G]
    (P : Subgroup (Equiv.Perm G)) (𝓑 : Set (Set G)) : Prop :=
  (∀ B, B ∈ 𝓑 → B.ncard = 2) ∧
    (∀ x : G, ∃! B : Set G, B ∈ 𝓑 ∧ x ∈ B) ∧
      (∀ p : Equiv.Perm G, p ∈ P → ∀ B : Set G, B ∈ 𝓑 → p '' B ∈ 𝓑)

def additiveCoset {G : Type*} [Add G] (g : G) (K : Set G) : Set G :=
  {x | ∃ k ∈ K, x = g + k}

def regularTwoPointBlocksAreCosets : Prop :=
  ∀ {G : Type u} [Fintype G] [AddGroup G]
    (P : Subgroup (Equiv.Perm G)) (𝓑 : Set (Set G)),
    (∀ g : G, Equiv.addLeft g ∈ P) →
      twoPointBlockSystem P 𝓑 →
        ∀ B₀ : Set G, B₀ ∈ 𝓑 → (0 : G) ∈ B₀ →
          ∃ K : AddSubgroup G,
            (K : Set G).ncard = 2 ∧ B₀ = (K : Set G) ∧
              ∀ B : Set G, B ∈ 𝓑 → ∃ g : G, B = additiveCoset g (K : Set G)

abbrev BinaryNineGroup (r : ℕ) := BinaryVector r × CyclicNine

def orderTwoSubgroupsOfBinaryNine : Prop :=
  ∀ {r : ℕ} (K : AddSubgroup (BinaryNineGroup r)),
    (K : Set (BinaryNineGroup r)).ncard = 2 →
      ∃! v : BinaryVector r,
        v ≠ 0 ∧ K = AddSubgroup.zmultiples (v, (0 : CyclicNine))

def regularC2rC9TwoPointBlockClaim : Prop :=
  regularTwoPointBlocksAreCosets.{u} ∧ orderTwoSubgroupsOfBinaryNine

/-! Claim 38168: parity in the regular C₃² × C₂ action. -/

abbrev TernaryPlane := ZMod 3 × ZMod 3
abbrev RegularTernaryBinaryGroup := TernaryPlane × ZMod 2

def regularC3SquaredC2Parity : Prop :=
  (∀ h : RegularTernaryBinaryGroup,
      Equiv.Perm.sign (Equiv.addLeft h) =
        if h.2 = 0 then (1 : ℤˣ) else (-1 : ℤˣ)) ∧
    addOrderOf (((0 : TernaryPlane), (1 : ZMod 2))) = 2 ∧
    Equiv.Perm.cycleType
        (Equiv.addLeft (((0 : TernaryPlane), (1 : ZMod 2)))) =
      Multiset.replicate 9 2 ∧
    (∀ a : TernaryPlane, a ≠ 0 →
      addOrderOf (a, (1 : ZMod 2)) = 6 ∧
      Equiv.Perm.cycleType (Equiv.addLeft (a, (1 : ZMod 2))) =
        Multiset.replicate 3 6)

/-! Claim 38184: perfect, pairwise-surjective subgroups are products. -/

def isPerfectGroup (D : Type*) [Group D] : Prop :=
  Subgroup.closure
      {z : D | ∃ a b : D, z = a * b * a⁻¹ * b⁻¹} = ⊤

def pairwiseTwoSurjective {D : Type*} [Group D] {n : ℕ}
    (S : Subgroup (Fin n → D)) : Prop :=
  ∀ i j : Fin n, i ≠ j →
    ∀ a b : D, ∃ x : Fin n → D, x ∈ S ∧ x i = a ∧ x j = b

def perfectPairwiseSurjectiveFullProduct {D : Type*} [Group D] {n : ℕ}
    (S : Subgroup (Fin n → D)) : Prop :=
  2 ≤ n → isPerfectGroup D → pairwiseTwoSurjective S → S = ⊤

/-! Claims 38228 and 38234: the finite S₄ census. -/

def isTwoSubgroup {G : Type*} [Group G] (P : Subgroup G) : Prop :=
  ∃ k : ℕ, Nat.card P = 2 ^ k

def isRegularPermutationSubgroup {α : Type*}
    (C : Subgroup (Equiv.Perm α)) : Prop :=
  ∀ x y : α, ∃! g : C, g.1 x = y

def isRegularCyclicFour (C : Subgroup (Equiv.Perm (Fin 4))) : Prop :=
  Nat.card C = 4 ∧
    (∃ σ : Equiv.Perm (Fin 4),
      C = Subgroup.closure ({σ} : Set (Equiv.Perm (Fin 4))) ∧ orderOf σ = 4) ∧
      isRegularPermutationSubgroup C

def isFourCycle (σ : Equiv.Perm (Fin 4)) : Prop :=
  orderOf σ = 4

def uniqueRegularCyclicFourInTwoSubgroup : Prop :=
  (∀ P : Subgroup (Equiv.Perm (Fin 4)), isTwoSubgroup P →
    ∀ C₁ C₂ : Subgroup (Equiv.Perm (Fin 4)),
      C₁ ≤ P → C₂ ≤ P → isRegularCyclicFour C₁ →
        isRegularCyclicFour C₂ → C₁ = C₂) ∧
  (∀ σ : Equiv.Perm (Fin 4), isFourCycle σ →
    Nat.card (Subgroup.normalizer
      (↑(Subgroup.closure ({σ} : Set (Equiv.Perm (Fin 4)))) :
        Set (Equiv.Perm (Fin 4)))) = 8) ∧
  (∀ (P : Subgroup (Equiv.Perm (Fin 4)))
      (σ : Equiv.Perm (Fin 4)),
      isTwoSubgroup P → σ ∈ P → isFourCycle σ →
        P ≤ Subgroup.normalizer
          (↑(Subgroup.closure ({σ} : Set (Equiv.Perm (Fin 4)))) :
            Set (Equiv.Perm (Fin 4)))) ∧
  (∀ σ τ : Equiv.Perm (Fin 4), isFourCycle σ → isFourCycle τ →
    isTwoSubgroup
      (Subgroup.closure ({σ, τ} : Set (Equiv.Perm (Fin 4)))) →
      Subgroup.closure ({σ} : Set (Equiv.Perm (Fin 4))) =
          Subgroup.closure ({τ} : Set (Equiv.Perm (Fin 4))) ∧
        σ ^ 2 = τ ^ 2)

def regularCyclicFourIncidence : Type :=
  Σ P : {P : Subgroup (Equiv.Perm (Fin 4)) // isTwoSubgroup P},
    {C : Subgroup (Equiv.Perm (Fin 4)) //
      C ≤ P.1 ∧ isRegularCyclicFour C}

def twoGroupFourCyclePair : Type :=
  {p : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) //
    isFourCycle p.1 ∧ isFourCycle p.2 ∧
      isTwoSubgroup
        (Subgroup.closure ({p.1, p.2} : Set (Equiv.Perm (Fin 4))))}

def exactS4Census : Prop :=
  Nat.card (Subgroup (Equiv.Perm (Fin 4))) = 30 ∧
    Nat.card {P : Subgroup (Equiv.Perm (Fin 4)) // isTwoSubgroup P} = 20 ∧
    Nat.card regularCyclicFourIncidence = 6 ∧
    (∀ P : Subgroup (Equiv.Perm (Fin 4)), isTwoSubgroup P →
      ∀ C₁ C₂ : Subgroup (Equiv.Perm (Fin 4)),
        C₁ ≤ P → C₂ ≤ P → isRegularCyclicFour C₁ →
          isRegularCyclicFour C₂ → C₁ = C₂) ∧
    Nat.card {p : (Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4)) //
      isFourCycle p.1 ∧ isFourCycle p.2} = 36 ∧
    Nat.card twoGroupFourCyclePair = 12 ∧
    (∀ p : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4),
      isFourCycle p.1 → isFourCycle p.2 →
        isTwoSubgroup
          (Subgroup.closure ({p.1, p.2} : Set (Equiv.Perm (Fin 4)))) →
        Nat.card (Subgroup.closure
          ({p.1, p.2} : Set (Equiv.Perm (Fin 4)))) = 4 ∧
        Subgroup.closure ({p.1} : Set (Equiv.Perm (Fin 4))) =
          Subgroup.closure ({p.2} : Set (Equiv.Perm (Fin 4))) ∧
        p.1 ^ 2 = p.2 ^ 2)

/-! Claims 38297--38301: four projected characters over 𝔽₃. -/

abbrev TernaryDualCarrier := Fin 2 → ZMod 3
abbrev TernaryScalar := ZMod 3

def epsilonOne : TernaryDualCarrier →ₗ[TernaryScalar] TernaryScalar :=
  LinearMap.proj 0

def epsilonTwo : TernaryDualCarrier →ₗ[TernaryScalar] TernaryScalar :=
  LinearMap.proj 1

def epsilonPlus : TernaryDualCarrier →ₗ[TernaryScalar] TernaryScalar :=
  epsilonOne + epsilonTwo

def epsilonMinus : TernaryDualCarrier →ₗ[TernaryScalar] TernaryScalar :=
  epsilonOne - epsilonTwo

def fourCharacterSet : Set (TernaryDualCarrier →ₗ[TernaryScalar] TernaryScalar) :=
  {epsilonOne, epsilonTwo, epsilonPlus, epsilonMinus}

def projectedSlope {H : Type*} [AddCommGroup H]
    [Module TernaryScalar H]
    (L : (TernaryDualCarrier →ₗ[TernaryScalar] TernaryScalar) →
      Submodule TernaryScalar H)
    (C : H → TernaryDualCarrier)
    (θ : TernaryDualCarrier →ₗ[TernaryScalar] TernaryScalar)
    (h : L θ) : TernaryScalar :=
  θ (C h)

def constantProjectedDerivativesGiveLinearSlopes {H : Type*}
    [AddCommGroup H] [Module TernaryScalar H]
    [FiniteDimensional TernaryScalar H]
    (L : (TernaryDualCarrier →ₗ[TernaryScalar] TernaryScalar) →
      Submodule TernaryScalar H) (C : H → TernaryDualCarrier) : Prop :=
  C 0 = 0 →
    (∀ θ ∈ fourCharacterSet, ∀ h : H, h ∈ L θ →
      ∀ x : H, θ (C (x + h)) - θ (C x) = θ (C h)) →
      ∀ θ ∈ fourCharacterSet,
        ∃ bθ : L θ →ₗ[TernaryScalar] TernaryScalar,
          ∀ h : L θ, bθ h = projectedSlope L C θ h

def restrictionMapImageMembership {H : Type*}
    [AddCommGroup H] [Module TernaryScalar H]
    (L : (TernaryDualCarrier →ₗ[TernaryScalar] TernaryScalar) →
      Submodule TernaryScalar H)
    (b : (θ : TernaryDualCarrier →ₗ[TernaryScalar] TernaryScalar) →
      (L θ →ₗ[TernaryScalar] TernaryScalar)) : Prop :=
  ∃ ℓ : H →ₗ[TernaryScalar] TernaryDualCarrier,
    ∀ θ ∈ fourCharacterSet, ∀ h : L θ,
      θ (ℓ h) = b θ h

def explicitDualRestrictionObstruction {H : Type*}
    [AddCommGroup H] [Module TernaryScalar H]
    (L : (TernaryDualCarrier →ₗ[TernaryScalar] TernaryScalar) →
      Submodule TernaryScalar H) : Prop :=
  ∀ b : (θ : TernaryDualCarrier →ₗ[TernaryScalar] TernaryScalar) →
      (L θ →ₗ[TernaryScalar] TernaryScalar),
    ¬ restrictionMapImageMembership L b →
      ∃ xone : L epsilonOne, ∃ xtwo : L epsilonTwo,
        ∃ xplus : L epsilonPlus, ∃ xminus : L epsilonMinus,
          ((xone : H) + (xplus : H) + (xminus : H) = 0) ∧
            ((xtwo : H) + (xplus : H) - (xminus : H) = 0) ∧
              b epsilonOne xone + b epsilonTwo xtwo +
                  b epsilonPlus xplus + b epsilonMinus xminus ≠ 0

def commonPotentialFourCharacterGluing {H : Type*}
    [AddCommGroup H] [Module TernaryScalar H]
    [FiniteDimensional TernaryScalar H]
    (L : (TernaryDualCarrier →ₗ[TernaryScalar] TernaryScalar) →
      Submodule TernaryScalar H) : Prop :=
  ∀ C : H → TernaryDualCarrier, C 0 = 0 →
    (∀ θ ∈ fourCharacterSet, ∀ h : H, h ∈ L θ →
      ∀ x : H, θ (C (x + h)) - θ (C x) = θ (C h)) →
      ∃ ℓ : H →ₗ[TernaryScalar] TernaryDualCarrier,
        ∀ θ ∈ fourCharacterSet, ∀ h : L θ,
          θ (ℓ h) = θ (C h)

/-! Claim 39895: quotient fibers for C₃ × (C₂² × C₃²). -/

abbrev CommonBlockSubgroup := ZMod 3
abbrev QuotientTwoSquare := ZMod 2 × ZMod 2
abbrev QuotientThreeSquare := ZMod 3 × ZMod 3
abbrev QuotientFiberBase := QuotientTwoSquare × QuotientThreeSquare
abbrev QuotientFiberGroup := CommonBlockSubgroup × QuotientFiberBase

def quotientFiber (S : Set QuotientFiberGroup) (h : QuotientFiberBase) : Set QuotientFiberGroup :=
  S ∩ (Set.univ ×ˢ {h})

def quotientFiberColor (S : Set QuotientFiberGroup) : QuotientFiberBase → ℕ :=
  fun h => (quotientFiber S h).ncard

/-! Claim 40801: angle bounds for triangles with side lengths in [1, 11/10]. -/

def goodTriangleSides (a b c : ℝ) : Prop :=
  1 ≤ a ∧ a ≤ (11 : ℝ) / 10 ∧
    1 ≤ b ∧ b ≤ (11 : ℝ) / 10 ∧
      1 ≤ c ∧ c ≤ (11 : ℝ) / 10 ∧
        a < b + c ∧ b < a + c ∧ c < a + b

def triangleCosineA (a b c : ℝ) : ℝ :=
  (b ^ 2 + c ^ 2 - a ^ 2) / (2 * b * c)

def triangleCosineB (a b c : ℝ) : ℝ :=
  (a ^ 2 + c ^ 2 - b ^ 2) / (2 * a * c)

def triangleCosineC (a b c : ℝ) : ℝ :=
  (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b)

def strictAngleIntervalForGoodTriangles : Prop :=
  ∀ a b c : ℝ, goodTriangleSides a b c →
    let α := Real.arccos (triangleCosineA a b c)
    let β := Real.arccos (triangleCosineB a b c)
    let γ := Real.arccos (triangleCosineC a b c)
    (79 / 200 : ℝ) ≤ Real.cos α ∧ Real.cos α ≤ (71 / 121 : ℝ) ∧
        3 * Real.pi / 10 < α ∧ α < 2 * Real.pi / 5 ∧
      (79 / 200 : ℝ) ≤ Real.cos β ∧ Real.cos β ≤ (71 / 121 : ℝ) ∧
        3 * Real.pi / 10 < β ∧ β < 2 * Real.pi / 5 ∧
      (79 / 200 : ℝ) ≤ Real.cos γ ∧ Real.cos γ ≤ (71 / 121 : ℝ) ∧
        3 * Real.pi / 10 < γ ∧ γ < 2 * Real.pi / 5

/-! Claim 41497: stabilizer orbits constrain the 2-closure. -/

def pointStabilizerSet {Ω : Type*}
    (G : Subgroup (Equiv.Perm Ω)) (zero : Ω) : Set (Equiv.Perm Ω) :=
  {g | g ∈ G ∧ g zero = zero}

def permutationOrbit {Ω : Type*}
    (P : Set (Equiv.Perm Ω)) (x : Ω) : Set Ω :=
  {y | ∃ g : Equiv.Perm Ω, g ∈ P ∧ g x = y}

def twoClosureMembership {Ω : Type*}
    (G : Subgroup (Equiv.Perm Ω)) (q : Equiv.Perm Ω) : Prop :=
  ∀ x y : Ω, ∃ g : Equiv.Perm Ω,
    g ∈ G ∧ q x = g x ∧ q y = g y

def stabilizerOrbitTwoClosureNecessaryCondition {Ω : Type*}
    (G : Subgroup (Equiv.Perm Ω)) (zero : Ω) : Prop :=
  ∀ q : Equiv.Perm Ω, q zero = zero →
    (twoClosureMembership G q →
      ∀ x : Ω,
        q '' permutationOrbit (pointStabilizerSet G zero) x =
          permutationOrbit (pointStabilizerSet G zero) x) ∧
    ((∃ x : Ω,
        q '' permutationOrbit (pointStabilizerSet G zero) x ≠
          permutationOrbit (pointStabilizerSet G zero) x) →
      ¬ twoClosureMembership G q)

end MathlibPlus.Open.ResearchFormalizationBatch
