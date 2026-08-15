import Mathlib

open scoped BigOperators Topology

namespace MathlibPlus.Open.ResearchFormalization

/-- Translation of a finitely supported integer packet. -/
def claim4620 : Prop :=
  let shiftPacket : ℝ → (ℝ →₀ ℤ) → (ℝ →₀ ℤ) := fun a p =>
    p.mapDomain (fun x => x + a)
  ∀ (a b : ℝ) (p : ℝ →₀ ℤ),
    shiftPacket 0 p = p ∧
      shiftPacket b (shiftPacket a p) = shiftPacket (a + b) p ∧
      shiftPacket (-a) (shiftPacket a p) = p

/-- The explicitly defined central-difference shear fixes zero but is not affine. -/
def claim5926 : Prop :=
  ∀ p : ℕ, Nat.Prime p → 5 ≤ p →
    let V := Fin 6 → ZMod p
    let q : ZMod p → ZMod p := fun s => s * (s - 1) * (2 : ZMod p)⁻¹
    let F : V → V := fun v =>
      ![v 0, v 1, v 2 + q (v 0 + v 4), v 3, v 4,
        v 5 + q (v 0 + v 4)]
    F 0 = 0 ∧
      (∃ v : V, q (v 0 + v 4) ≠ 0) ∧
      ¬∃ (L : V →ₗ[ZMod p] V) (b : V), ∀ v : V, F v = L v + b

end MathlibPlus.Open.ResearchFormalization
