import Mathlib
import MathlibPlus.Open.ResearchFormalization.Grid

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Grid

abbrev Claim36139BulkEdge (p q : ℕ) :=
  (Fin p × Fin (q - 1)) ⊕ (Fin (p - 1) × Fin q)

abbrev Claim36139VirtualChord (p q : ℕ) :=
  Fin (q - 1) ⊕ Fin (p - 1)

def claim36139_bulkEdgeCount (p q : ℕ) : Prop :=
  Fintype.card (Claim36139BulkEdge p q) =
    p * (q - 1) + q * (p - 1)

def claim36139_virtualChordCount (p q : ℕ) : Prop :=
  Fintype.card (Claim36139VirtualChord p q) = p + q - 2

def claim36139_interiorEquilibrium
    (p q : ℕ) (a b : ℕ → ℕ → ℝ) (u v : Plane) : Prop :=
  ∀ (i j : ℕ),
    1 ≤ i → i < p → 1 ≤ j → j < q →
      (a (i - 1) j - a i j) • u +
        (b i (j - 1) - b i j) • v = 0

def claim36139_linewiseValues
    (p q : ℕ) (a b : ℕ → ℕ → ℝ)
    (ρ : InteriorRow q → ℝ) (κ : InteriorColumn p → ℝ) : Prop :=
  (∀ (i j : ℕ) (hi : i < p) (hj₁ : 1 ≤ j) (hjq : j < q),
    a i j = ρ ⟨j, hj₁, hjq⟩) ∧
  (∀ (i j : ℕ) (hi₁ : 1 ≤ i) (hip : i < p) (hj : j < q),
    b i j = κ ⟨i, hi₁, hip⟩)

def claim36139_rowForceCondensation
    (p q : ℕ) (u : Plane) (ρ : InteriorRow q → ℝ) : Prop :=
  ∀ j : InteriorRow q,
    chainForceAt p (ρ j) u ⟨0, Nat.zero_lt_succ p⟩ = (-ρ j) • u ∧
    chainForceAt p (ρ j) u ⟨p, Nat.lt_succ_self p⟩ = ρ j • u ∧
    (∀ k : Fin (p + 1), 0 < k.1 → k.1 < p →
      chainForceAt p (ρ j) u k = 0) ∧
    (-ρ j) • u =
      -(ρ j / (p : ℝ)) • ((p : ℝ) • u) ∧
    ρ j • u =
      (ρ j / (p : ℝ)) • ((p : ℝ) • u)

def claim36139_columnForceCondensation
    (p q : ℕ) (v : Plane) (κ : InteriorColumn p → ℝ) : Prop :=
  ∀ i : InteriorColumn p,
    chainForceAt q (κ i) v ⟨0, Nat.zero_lt_succ q⟩ = (-κ i) • v ∧
    chainForceAt q (κ i) v ⟨q, Nat.lt_succ_self q⟩ = κ i • v ∧
    (∀ k : Fin (q + 1), 0 < k.1 → k.1 < q →
      chainForceAt q (κ i) v k = 0) ∧
    (-κ i) • v =
      -(κ i / (q : ℝ)) • ((q : ℝ) • v) ∧
    κ i • v =
      (κ i / (q : ℝ)) • ((q : ℝ) • v)

def claim36139_virtualChordGeometry
    (p q : ℕ) (u v : Plane)
    (x : Fin (p + 1) → Fin (q + 1) → Plane) : Prop :=
  (∀ j : InteriorRow q,
    x ⟨p, Nat.lt_succ_self p⟩
        ⟨j.1, Nat.lt_succ_of_lt j.2.2⟩ -
      x ⟨0, Nat.zero_lt_succ p⟩
        ⟨j.1, Nat.lt_succ_of_lt j.2.2⟩ =
      (p : ℝ) • u) ∧
  (∀ i : InteriorColumn p,
    x ⟨i.1, Nat.lt_succ_of_lt i.2.2⟩
        ⟨q, Nat.lt_succ_self q⟩ -
      x ⟨i.1, Nat.lt_succ_of_lt i.2.2⟩
        ⟨0, Nat.zero_lt_succ q⟩ =
      (q : ℝ) • v)

def claim36139_secondMomentCondensation
    (p q : ℕ) (u v : Plane)
    (ρ : InteriorRow q → ℝ) (κ : InteriorColumn p → ℝ) : Prop :=
  (∀ j : InteriorRow q,
    (((p : ℝ) * ρ j) • outerProduct u u =
      (ρ j / (p : ℝ)) •
        outerProduct ((p : ℝ) • u) ((p : ℝ) • u))) ∧
  (∀ i : InteriorColumn p,
    (((q : ℝ) * κ i) • outerProduct v v =
      (κ i / (q : ℝ)) •
        outerProduct ((q : ℝ) • v) ((q : ℝ) • v)))

def claim36139_nonnegativeSupport
    (p q : ℕ) (a b : ℕ → ℕ → ℝ)
    (ρ : InteriorRow q → ℝ) (κ : InteriorColumn p → ℝ) : Prop :=
  ((∀ (i j : ℕ), i < p → j ≤ q → 0 ≤ a i j) ∧
    (∀ (i j : ℕ), i ≤ p → j < q → 0 ≤ b i j)) →
  ((∀ j : InteriorRow q,
      0 ≤ ρ j ∧ 0 ≤ ρ j / (p : ℝ)) ∧
    (∀ i : InteriorColumn p,
      0 ≤ κ i ∧ 0 ≤ κ i / (q : ℝ)))

/-- The exact boundary-order condensation theorem for a flat affine grid:
interior equilibrium makes stresses linewise constant, every bulk row or
column is replaced by its boundary chord with the same force and second
moment, and nonnegative support coefficients remain nonnegative. -/
def claim36139 : Prop :=
  ∀ (p q : ℕ) (u v : Plane)
    (x : Fin (p + 1) → Fin (q + 1) → Plane)
    (a b : ℕ → ℕ → ℝ),
    1 ≤ p → 1 ≤ q →
    affineParallelogramGrid p q u v x
      (fun i j => a i.1 j.1) (fun i j => b i.1 j.1) →
    claim36139_interiorEquilibrium p q a b u v →
    claim36139_bulkEdgeCount p q ∧
    claim36139_virtualChordCount p q ∧
    ∃ (ρ : InteriorRow q → ℝ) (κ : InteriorColumn p → ℝ),
      claim36139_linewiseValues p q a b ρ κ ∧
      claim36139_virtualChordGeometry p q u v x ∧
      claim36139_rowForceCondensation p q u ρ ∧
      claim36139_columnForceCondensation p q v κ ∧
      claim36139_secondMomentCondensation p q u v ρ κ ∧
      claim36139_nonnegativeSupport p q a b ρ κ

end MathlibPlus.Open.ResearchFormalization.Grid
