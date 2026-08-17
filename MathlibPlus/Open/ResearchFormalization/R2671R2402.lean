import Mathlib
import MathlibPlus.Open.ResearchFormalization.GraphDeckBatch

namespace MathlibPlus.Open.ResearchFormalization.R2671R2402

noncomputable section
open Classical
open scoped BigOperators

abbrev Five := Fin 5

def listedEdgeG1 (x y : Five) : Prop :=
  (x = 0 ∧ y = 3) ∨
    (x = 0 ∧ y = 4) ∨
      (x = 1 ∧ y = 4) ∨
        (x = 2 ∧ y = 4) ∨
          (x = 3 ∧ y = 4)

def listedEdgeG2 (x y : Five) : Prop :=
  (x = 0 ∧ y = 3) ∨
    (x = 1 ∧ y = 3) ∨
      (x = 0 ∧ y = 4) ∨
        (x = 2 ∧ y = 4) ∨
          (x = 3 ∧ y = 4)

def graphG1 : SimpleGraph Five := SimpleGraph.fromRel listedEdgeG1
def graphG2 : SimpleGraph Five := SimpleGraph.fromRel listedEdgeG2

/-- Claim 43506: the explicit equal-leaf-deck witness is separated by the
maximum-degree statistic. -/
def claim43506_pureLayerSeparation : Prop :=
  SimpleGraph.maxDegree graphG1 = 4 ∧
    SimpleGraph.maxDegree graphG2 = 3 ∧
    MathlibPlus.Open.ResearchFormalization.leafDeckEqual graphG1 graphG2 ∧
      ¬ Nonempty (graphG1 ≃g graphG2)

/-- Zero extension of a finite complex packet to all natural window indices. -/
def zeroPadded {L : ℕ} (z : Fin L → ℂ) (j : ℕ) : ℂ :=
  if h : j < L then z ⟨j, h⟩ else 0

def scalarWindow {n : ℕ}
    (z : Fin (2 * n - 1) → ℂ)
    (r : Fin ((2 * n - 1) + (n - 1) - 1)) : ℂ :=
  let H := n - 1
  ∑ j : Fin H,
    if H ≤ r.1 + 1 + j.1 then
      zeroPadded z (r.1 + 1 + j.1 - H)
    else 0

def scalarMass {L : ℕ} (z : Fin L → ℂ) : ℂ :=
  ∑ j : Fin L, z j

def scalarPacketCost (n : ℕ) (z : Fin (2 * n - 1) → ℂ) : ℝ :=
  let H := n - 1
  (1 / (H : ℝ)) *
    ∑ r : Fin ((2 * n - 1) + (n - 1) - 1),
      ‖scalarWindow z r‖ ^ 2

def threeCombPacket (n : ℕ) : Fin (2 * n - 1) → ℂ :=
  fun j =>
    if j.1 = 0 ∨ j.1 = n - 1 ∨ j.1 = 2 * n - 2 then
      (1 / 3 : ℂ)
    else 0

/-- Claim 43632: among total-mass-one scalar packets, the zero-padded
length-`H` window cost is at least `1/3`, and the exact three-comb attains it. -/
def claim43632_scalarPacketCostOptimality : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (∀ z : Fin (2 * n - 1) → ℂ,
      scalarMass z = 1 →
        (∑ r : Fin ((2 * n - 1) + (n - 1) - 1), scalarWindow z r =
            (n - 1 : ℂ)) ∧
          scalarPacketCost n z ≥ (1 / 3 : ℝ)) ∧
    scalarMass (threeCombPacket n) = 1 ∧
      scalarPacketCost n (threeCombPacket n) = (1 / 3 : ℝ) ∧
        ∀ z : Fin (2 * n - 1) → ℂ,
          scalarMass z = 1 →
            scalarPacketCost n z ≥ scalarPacketCost n (threeCombPacket n)

end
end MathlibPlus.Open.ResearchFormalization.R2671R2402
