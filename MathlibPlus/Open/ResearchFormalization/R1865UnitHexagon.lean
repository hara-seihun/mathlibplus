import MathlibPlus.Geometry.Claim35609

namespace MathlibPlus.Open.ResearchFormalization.R1865UnitHexagon

noncomputable section

/-- Claim 34467: the repaired six-vertex certificate is retained together
with its exact unit graph and triangle-free six-cycle conclusion. -/
def explicitUnitHexagonCertificate_claim34467 : Prop :=
    let s : ℝ := Real.sqrt 2
    let a : ℝ := s⁻¹
    let u : ℝ × ℝ := (1, 0)
    let v : ℝ × ℝ := (0, 1)
    let w : ℝ × ℝ := (-a, a)
    let p : Fin 6 → ℝ × ℝ :=
      ![(0, 0), u, u + v, u + v + w,
        u + v + w - u, u + v + w - u - v]
    let d (x y : ℝ × ℝ) : ℝ :=
      (x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2
    let turn (x y : ℝ × ℝ) : ℝ := x.1 * y.2 - x.2 * y.1
    let adjacent (i j : Fin 6) : Prop :=
      (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
      (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
      (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
      (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) ∨
      (i = 4 ∧ j = 5) ∨ (i = 5 ∧ j = 4) ∨
      (i = 5 ∧ j = 0) ∨ (i = 0 ∧ j = 5)
    s ^ 2 = 2 ∧ 0 < s ∧
    (d (p 0) (p 1) = 1 ∧ d (p 1) (p 2) = 1 ∧
      d (p 2) (p 3) = 1 ∧ d (p 3) (p 4) = 1 ∧
      d (p 4) (p 5) = 1 ∧ d (p 5) (p 0) = 1) ∧
    (turn (p 5 - p 4) (p 0 - p 5) > 0 ∧
      turn (p 0 - p 5) (p 1 - p 0) > 0 ∧
      turn (p 1 - p 0) (p 2 - p 1) > 0 ∧
      turn (p 2 - p 1) (p 3 - p 2) > 0 ∧
      turn (p 3 - p 2) (p 4 - p 3) > 0 ∧
      turn (p 4 - p 3) (p 5 - p 4) > 0) ∧
    (p 1 - p 0 = u ∧ p 2 - p 1 = v ∧ p 3 - p 2 = w ∧
      p 4 - p 3 = -u ∧ p 5 - p 4 = -v ∧ p 0 - p 5 = -w) ∧
    (∀ i j : Fin 6, i ≠ j → (d (p i) (p j) = 1 ↔ adjacent i j)) ∧
    (d (p 0) (p 2) = 2 ∧ d (p 0) (p 3) = 3 ∧
      d (p 0) (p 4) = 2 + s ∧ d (p 1) (p 3) = 2 + s ∧
      d (p 1) (p 4) = 3 + 2 * s ∧ d (p 1) (p 5) = 2 + s ∧
      d (p 2) (p 4) = 2 + s ∧ d (p 2) (p 5) = 3 ∧
      d (p 3) (p 5) = 2) ∧
    (∀ i j k : Fin 6,
      i ≠ j → i ≠ k → j ≠ k →
      ¬(d (p i) (p j) = 1 ∧ d (p j) (p k) = 1 ∧ d (p k) (p i) = 1))

end

end MathlibPlus.Open.ResearchFormalization.R1865UnitHexagon
