import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.StaticPacketRoundingObstruction61203

noncomputable section

/-- The packet counts `(2,3,1,1,1)`, indexed by `Fin 5`. -/
def packetCount (r : Fin 5) : ℕ :=
  if r.val = 0 then 2 else if r.val = 1 then 3 else 1

/-- The disjoint union of the five packet sets. -/
abbrev Packet := Σ r : Fin 5, Fin (packetCount r)

/-- The one-based level of a packet. -/
def packetLevel (j : Packet) : ℕ := j.1.val + 1

/-- The requester mass in the exact five-level construction. -/
def packetMass (j : Packet) : ℝ := (1 : ℝ) / packetCount j.1

/-- The energy in the exact five-level construction. -/
def packetEnergy (j : Packet) : ℝ := (packetCount j.1 : ℝ) / 16

/-- All deterministic static coordinate orders of the eight packets. -/
abbrev StaticOrder := Packet ≃ Fin 8

/-- The one-based position of a packet in a deterministic order. -/
def packetRank (π : StaticOrder) (j : Packet) : ℕ := (π.toFun j).val + 1

/-- The static scalar packet cost. -/
def packetCost (π : StaticOrder) : ℝ :=
  ∑ j : Packet,
    (packetRank π j : ℝ) * packetMass j * packetEnergy j

/-- The level-weighted component-energy budget. -/
def packetBudget : ℝ :=
  ∑ j : Packet, (packetLevel j : ℝ) * packetEnergy j

/-- A probability distribution on deterministic static orders. -/
def orderDistribution (p : StaticOrder → ℝ) : Prop :=
  let _ : DecidableEq Packet := Classical.decEq _
  (∀ π : StaticOrder, 0 ≤ p π) ∧
    (∑ π : StaticOrder, p π) = 1

/-- Expected static cost under a distribution on orders. -/
def expectedPacketCost (p : StaticOrder → ℝ) : ℝ :=
  let _ : DecidableEq Packet := Classical.decEq _
  ∑ π : StaticOrder, p π * packetCost π

/-- The scalar coefficient-one assertion for arbitrary finite packet systems. -/
def genericLevelWeight {α : Type*} [Fintype α]
    {k : ℕ} (level : α → Fin k) (j : α) : ℝ :=
  (level j).val + 1

/-- Rank cost for an arbitrary finite packet system. -/
def genericPacketCost {α : Type*} [Fintype α]
    {levelCount : ℕ} (level : α → Fin levelCount)
    (mass energy : α → ℝ)
    (π : α ≃ Fin (Fintype.card α)) : ℝ :=
  ∑ j : α,
    ((π.toFun j).val + 1 : ℝ) * mass j * energy j

/-- Level-weighted budget for an arbitrary finite packet system. -/
def genericPacketBudget {α : Type*} [Fintype α]
    {levelCount : ℕ} (level : α → Fin levelCount)
    (energy : α → ℝ) : ℝ :=
  ∑ j : α, genericLevelWeight level j * energy j

/-- A probability distribution on arbitrary finite static orders. -/
def genericOrderDistribution {α : Type*} [Fintype α]
    (p : (α ≃ Fin (Fintype.card α)) → ℝ) : Prop :=
  let _ : DecidableEq α := Classical.decEq _
  (∀ π, 0 ≤ p π) ∧
    (∑ π, p π) = 1

/-- Expected rank cost for an arbitrary finite static order distribution. -/
def genericExpectedPacketCost {α : Type*} [Fintype α]
    {levelCount : ℕ} (level : α → Fin levelCount)
    (mass energy : α → ℝ)
    (p : (α ≃ Fin (Fintype.card α)) → ℝ) : ℝ :=
  let _ : DecidableEq α := Classical.decEq _
  ∑ π, p π * genericPacketCost level mass energy π

/-- The universal deterministic-or-privately-randomized coefficient-one
rounding assertion refuted by the explicit packet system. -/
def universalCoefficientOne : Prop :=
  ∀ (α : Type) [Fintype α] (levelCount : ℕ)
    (level : α → Fin levelCount) (mass energy : α → ℝ),
    (∀ j, 0 ≤ energy j ∧ energy j ≤ mass j) →
    (∀ r : Fin levelCount,
      (∑ j : α, if level j = r then mass j else 0) ≤ 1) →
    (∑ j : α, energy j ≤ 1) →
    ((∃ π : α ≃ Fin (Fintype.card α),
        genericPacketCost level mass energy π ≤
          genericPacketBudget level energy) ∨
      (∃ p : (α ≃ Fin (Fintype.card α)) → ℝ,
        genericOrderDistribution p ∧
          genericExpectedPacketCost level mass energy p ≤
            genericPacketBudget level energy))

/-- The exact scalar premises, costs, and obstruction for Claim 61203. -/
def claim_61203_exact_five_level_static_scalar_packet_rounding_obstruction : Prop :=
  (packetCount (0 : Fin 5) = 2 ∧
    packetCount (1 : Fin 5) = 3 ∧
    packetCount (2 : Fin 5) = 1 ∧
    packetCount (3 : Fin 5) = 1 ∧
    packetCount (4 : Fin 5) = 1 ∧
    Fintype.card Packet = 8) ∧
  (∀ j : Packet,
    0 ≤ packetEnergy j ∧ packetEnergy j ≤ packetMass j) ∧
  (∀ r : Fin 5,
    (∑ j : Packet, if j.1 = r then packetMass j else 0) = 1) ∧
  (∑ j : Packet, packetEnergy j) = 1 ∧
  (∀ j : Packet, packetMass j * packetEnergy j = (1 : ℝ) / 16) ∧
  packetBudget =
    ((1 : ℝ) * 2 ^ 2 + 2 * 3 ^ 2 + 3 * 1 ^ 2 +
      4 * 1 ^ 2 + 5 * 1 ^ 2) / 16 ∧
  packetBudget = 17 / 8 ∧
  (∀ π : StaticOrder,
    packetCost π = (1 : ℝ) / 16 *
        (∑ a : Fin 8, (a.val + 1 : ℝ)) ∧
      packetCost π = 9 / 4 ∧
      packetCost π > packetBudget ∧
      packetCost π - packetBudget = 1 / 8 ∧
      packetCost π / packetBudget = 18 / 17) ∧
  (∀ p : StaticOrder → ℝ,
    orderDistribution p →
      expectedPacketCost p = 9 / 4 ∧
        expectedPacketCost p > packetBudget) ∧
  ¬ universalCoefficientOne

end

end MathlibPlus.Open.ResearchFormalization.StaticPacketRoundingObstruction61203
