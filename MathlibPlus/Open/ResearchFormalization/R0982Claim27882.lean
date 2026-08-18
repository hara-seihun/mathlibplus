import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0982Claim27882

noncomputable section

abbrev Plane (p : ℕ) := ZMod p × ZMod p
abbrev Fiber (p : ℕ) := Fin 3 → ZMod p
abbrev H (p : ℕ) := Plane p × Fiber p
abbrev E (p : ℕ) := ZMod p × H p

/-- The quadratic fibre shift from the rank-five quotient. -/
def quadraticF (p : ℕ) (u : Plane p) : Fiber p :=
  ![u.1 * (u.1 - 1), ((2 : ZMod p) * u.1 - 1) * u.2, u.2 ^ 2]

/-- The additive derivative of the plane-fibre function. -/
def derivativePhi (p : ℕ) (φ : Plane p → ZMod p)
    (u c : Plane p) : ZMod p :=
  φ (u + c) - φ u - φ c

/-- The displayed polar derivative of `F`, in its two generating directions. -/
def derivativeF (p : ℕ) (u c : Plane p) : Fiber p :=
  (2 * c.1) • ![u.1, u.2, 0] +
    (2 * c.2) • ![0, u.1, u.2]

/-- The displayed action of `q_phi`. -/
def qPhiSpec (p : ℕ) (φ : Plane p → ZMod p)
    (q : Equiv.Perm (E p)) : Prop :=
  ∀ z u w,
    q (z, (u, w)) = (z + φ u, (u, w + quadraticF p u))

/-- The graph component of the relative derivative above `u` and shift `c`.
The middle plane coordinate is the shift and is omitted from the graph vector. -/
def relativeDerivativeGraph (p : ℕ) (q : Equiv.Perm (E p))
    (u c : Plane p) : ZMod p × Fiber p :=
  let d := q⁻¹ (q (0, (u + c, 0)) - q (0, (u, 0)))
  (d.1, d.2.2)

/-- Claim 27882: over every odd prime, the relative derivative of the exact
plane-fibre transporter has the displayed `D_u phi` and `D_u F` components. -/
def claim27882 : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p) (_hodd : Odd p),
    letI : Fact p.Prime := ⟨hp⟩
    ∀ (φ : Plane p → ZMod p), φ 0 = 0 →
      ∃ q : Equiv.Perm (E p),
        qPhiSpec p φ q ∧
          ∀ u c : Plane p,
            relativeDerivativeGraph p q u c =
              (derivativePhi p φ u c, derivativeF p u c)

end

end MathlibPlus.Open.ResearchFormalization.R0982Claim27882
