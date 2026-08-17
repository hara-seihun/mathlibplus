import MathlibPlus.Open.ResearchFormalizationBatch.Frobenius21Claims

namespace MathlibPlus.Open.ResearchFormalization.R1416

noncomputable section

open MathlibPlus.Open.ResearchFormalizationBatch.Frobenius21Claims

abbrev C5 := Multiplicative (ZMod 5)
abbrev C3 := Multiplicative (ZMod 3)
abbrev C15 := Multiplicative (ZMod 15)
abbrev G5 := C5 × Frobenius21

/-- A block in the regular action of `G` is the translate of the subgroup
stabilizer `H`. -/
def regularBlock {G : Type*} [Group G] (H : Subgroup G) (x : G) : Set G :=
  (fun h : G => x * h) '' (H : Set G)

/-- The number of points in the block containing the identity. -/
def regularBlockSize {G : Type*} [Group G] (H : Subgroup G) : ℕ :=
  Set.ncard (regularBlock H 1)

/-- The intersection of all conjugates of a subgroup. -/
def coreOf {G : Type*} [Group G] (H : Subgroup G) : Subgroup G :=
  ⨅ g : G, H.comap (MulAut.conj g).toMonoidHom

/-- The quotient of the ambient regular group by the block-action kernel. -/
abbrev blockImageQuotient {G : Type*} [Group G] (H : Subgroup G) :=
  G ⧸ Subgroup.normalClosure (coreOf H : Set G)

/-- The quotient of the block point stabilizer by its kernel. -/
abbrev blockStabilizerQuotient {G : Type*} [Group G] (H : Subgroup G) :=
  H ⧸ Subgroup.normalClosure ((coreOf H).comap H.subtype : Set H)

/-- The induced action on blocks is regular exactly when its point
stabilizer is trivial. -/
def blockActionRegular {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  Nat.card (blockStabilizerQuotient H) = 1

/-- One row of the six-row table, including the block count, core order,
induced group, and regularity status. -/
def c5BlockRow (H : Subgroup G5) : Prop :=
  (regularBlockSize H = 3 ∧ Nat.card H = 3 ∧ Subgroup.index H = 35 ∧
      Nat.card (coreOf H) = 1 ∧
      Nonempty (blockImageQuotient H ≃* G5) ∧
      ¬ blockActionRegular H ∧ Nat.card (blockStabilizerQuotient H) = 3) ∨
    (regularBlockSize H = 5 ∧ Nat.card H = 5 ∧ Subgroup.index H = 21 ∧
      Nat.card (coreOf H) = 5 ∧
      Nonempty (blockImageQuotient H ≃* Frobenius21) ∧
      blockActionRegular H ∧ Nat.card (blockStabilizerQuotient H) = 1) ∨
    (regularBlockSize H = 7 ∧ Nat.card H = 7 ∧ Subgroup.index H = 15 ∧
      Nat.card (coreOf H) = 7 ∧
      Nonempty (blockImageQuotient H ≃* C15) ∧
      blockActionRegular H ∧ Nat.card (blockStabilizerQuotient H) = 1) ∨
    (regularBlockSize H = 15 ∧ Nat.card H = 15 ∧ Subgroup.index H = 7 ∧
      Nat.card (coreOf H) = 5 ∧
      Nonempty (blockImageQuotient H ≃* Frobenius21) ∧
      ¬ blockActionRegular H ∧ Nat.card (blockStabilizerQuotient H) = 3) ∨
    (regularBlockSize H = 21 ∧ Nat.card H = 21 ∧ Subgroup.index H = 5 ∧
      Nat.card (coreOf H) = 21 ∧
      Nonempty (blockImageQuotient H ≃* C5) ∧
      blockActionRegular H ∧ Nat.card (blockStabilizerQuotient H) = 1) ∨
    (regularBlockSize H = 35 ∧ Nat.card H = 35 ∧ Subgroup.index H = 3 ∧
      Nat.card (coreOf H) = 35 ∧
      Nonempty (blockImageQuotient H ≃* C3) ∧
      blockActionRegular H ∧ Nat.card (blockStabilizerQuotient H) = 1)

/-- Claim 36972: the complete proper nontrivial block table for
`C₅ × (C₇ : C₃)`. -/
def exactC5BlockTable_claim36972 : Prop :=
  ∀ H : Subgroup G5, H ≠ ⊥ → H ≠ ⊤ → c5BlockRow H

/-- Claim 36973: the two explicit nonregular complement rows. -/
def explicitComplementCounterexamples_claim36973 : Prop :=
  ∀ U : Subgroup Frobenius21, Nat.card U = 3 →
    let H₁ : Subgroup G5 := (⊥ : Subgroup C5).prod U
    let H₂ : Subgroup G5 := (⊤ : Subgroup C5).prod U
    coreOf H₁ = (⊥ : Subgroup G5) ∧
      regularBlockSize H₁ = 3 ∧
      Nat.card H₁ = 3 ∧
      Subgroup.index H₁ = 35 ∧
      Nonempty (blockImageQuotient H₁ ≃* G5) ∧
      Nat.card (blockImageQuotient H₁) = 105 ∧
      ¬ blockActionRegular H₁ ∧
      Nat.card (blockStabilizerQuotient H₁) = 3 ∧
      coreOf H₂ = (⊤ : Subgroup C5).prod (⊥ : Subgroup Frobenius21) ∧
      regularBlockSize H₂ = 15 ∧
      Nat.card H₂ = 15 ∧
      Subgroup.index H₂ = 7 ∧
      Nonempty (blockImageQuotient H₂ ≃* Frobenius21) ∧
      Nat.card (blockImageQuotient H₂) = 21 ∧
      ¬ blockActionRegular H₂ ∧
      Nat.card (blockStabilizerQuotient H₂) = 3

abbrev ControlGroup (p : ℕ) := Multiplicative (ZMod p)
abbrev ProductGroup (p : ℕ) := ControlGroup p × Frobenius21

/-- A row containing one of the two subgroups of the prime cyclic control,
with either the trivial, complement, normal `C₇`, or full Frobenius factor. -/
def threePrimeSubgroupRow (p : ℕ) (H : Subgroup (ProductGroup p)) : Prop :=
  H = (⊥ : Subgroup (ControlGroup p)).prod (⊥ : Subgroup Frobenius21) ∨
    (∃ U : Subgroup Frobenius21, Nat.card U = 3 ∧
      H = (⊥ : Subgroup (ControlGroup p)).prod U) ∨
    (∃ N : Subgroup Frobenius21,
      Nat.card N = 7 ∧ N.Normal ∧
        H = (⊥ : Subgroup (ControlGroup p)).prod N) ∨
    H = (⊥ : Subgroup (ControlGroup p)).prod (⊤ : Subgroup Frobenius21) ∨
    H = (⊤ : Subgroup (ControlGroup p)).prod (⊥ : Subgroup Frobenius21) ∨
    (∃ U : Subgroup Frobenius21, Nat.card U = 3 ∧
      H = (⊤ : Subgroup (ControlGroup p)).prod U) ∨
    (∃ N : Subgroup Frobenius21,
      Nat.card N = 7 ∧ N.Normal ∧
        H = (⊤ : Subgroup (ControlGroup p)).prod N) ∨
    H = (⊤ : Subgroup (ControlGroup p)).prod (⊤ : Subgroup Frobenius21)

/-- The complement-product rows are precisely the nonregular rows. -/
def complementProduct (p : ℕ) (H : Subgroup (ProductGroup p)) : Prop :=
  ∃ U : Subgroup Frobenius21, Nat.card U = 3 ∧
    (H = (⊥ : Subgroup (ControlGroup p)).prod U ∨
      H = (⊤ : Subgroup (ControlGroup p)).prod U)

/-- Claim 36975: the exact twenty-subgroup census for each of the three
prime-factor controls, with exactly fourteen nonregular complement rows. -/
def exactThreePrimeSubgroupCensus_claim36975 : Prop :=
  ∀ p : ℕ, (p = 2 ∨ p = 5 ∨ p = 11) →
    Nat.card (Subgroup (ProductGroup p)) = 20 ∧
      Nat.card {U : Subgroup Frobenius21 // Nat.card U = 3} = 7 ∧
      (∀ H : Subgroup (ProductGroup p), threePrimeSubgroupRow p H) ∧
      Nat.card {H : Subgroup (ProductGroup p) // complementProduct p H} = 14 ∧
      (∀ H : Subgroup (ProductGroup p),
        (Nat.card (blockStabilizerQuotient H) ≠ 1 ↔
          complementProduct p H) ∧
        (complementProduct p H →
          Nat.card (blockStabilizerQuotient H) = 3))

end

end MathlibPlus.Open.ResearchFormalization.R1416
