import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Grid

abbrev Plane := Fin 2 → ℝ

/-- The concrete two-vector linear-independence condition in `ℝ²`. -/
def linearlyIndependentPair (u v : Plane) : Prop :=
  ∀ a b : ℝ, a • u + b • v = 0 → a = 0 ∧ b = 0

/-- The affine parallelogram grid and its horizontal and vertical stress fields. -/
def affineParallelogramGrid
    (p q : ℕ) (u v : Plane)
    (x : Fin (p + 1) → Fin (q + 1) → Plane)
    (a : Fin p → Fin (q + 1) → ℝ)
    (b : Fin (p + 1) → Fin q → ℝ) : Prop :=
  linearlyIndependentPair u v ∧
    ∀ (i : Fin (p + 1)) (j : Fin (q + 1)),
      x i j = (i.1 : ℝ) • u + (j.1 : ℝ) • v

abbrev InteriorRow (q : ℕ) := {j : ℕ // 1 ≤ j ∧ j < q}
abbrev InteriorColumn (p : ℕ) := {i : ℕ // 1 ≤ i ∧ i < p}

/-- Linewise-constant interior horizontal and vertical stresses. -/
def linewiseConstantInteriorStress
    (p q : ℕ) (a b : ℕ → ℕ → ℝ) : Prop :=
  ∃ ρ : InteriorRow q → ℝ, ∃ κ : InteriorColumn p → ℝ,
    (∀ (i j : ℕ) (hi : i < p) (hj₁ : 1 ≤ j) (hjq : j < q),
      a i j = ρ ⟨j, hj₁, hjq⟩) ∧
    (∀ (i j : ℕ) (hi₁ : 1 ≤ i) (hip : i < p) (hj : j < q),
      b i j = κ ⟨i, hi₁, hip⟩)

/-- Net force at a vertex of a uniformly stressed finite path. -/
def chainForceAt (length : ℕ) (stress : ℝ) (direction : Plane)
    (k : Fin (length + 1)) : Plane :=
  ∑ e : Fin length,
    if k.1 = e.1 then -(stress • direction)
    else if k.1 = e.1 + 1 then stress • direction
    else 0

/-- Internal path forces cancel and the endpoint forces equal those of the
    corresponding virtual chord. -/
def rowForceCondensation : Prop :=
  ∀ (p q j : ℕ) (ρ : ℝ) (u : Plane),
    0 < p → 1 ≤ j → j < q →
      chainForceAt p ρ u ⟨0, Nat.zero_lt_succ p⟩ = (-ρ) • u ∧
      chainForceAt p ρ u ⟨p, Nat.lt_succ_self p⟩ = ρ • u ∧
      (∀ k : Fin (p + 1), 0 < k.1 → k.1 < p →
        chainForceAt p ρ u k = 0) ∧
      ((-ρ) • u, ρ • u) =
        (-(ρ / (p : ℝ)) • ((p : ℝ) • u),
          (ρ / (p : ℝ)) • ((p : ℝ) • u))

/-- Internal column forces cancel and the endpoint forces equal those of the
    corresponding virtual chord. -/
def columnForceCondensation : Prop :=
  ∀ (p q i : ℕ) (κ : ℝ) (v : Plane),
    0 < q → 1 ≤ i → i < p →
      chainForceAt q κ v ⟨0, Nat.zero_lt_succ q⟩ = (-κ) • v ∧
      chainForceAt q κ v ⟨q, Nat.lt_succ_self q⟩ = κ • v ∧
      (∀ k : Fin (q + 1), 0 < k.1 → k.1 < q →
        chainForceAt q κ v k = 0) ∧
      ((-κ) • v, κ • v) =
        (-(κ / (q : ℝ)) • ((q : ℝ) • v),
          (κ / (q : ℝ)) • ((q : ℝ) • v))

def outerProduct (u v : Plane) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun r c => u r * v c

/-- Row and column second moments, and their separate force cancellations, agree. -/
def exactSecondMomentCondensation : Prop :=
  ∀ (p q : ℕ) (ρ κ : ℝ) (u v : Plane),
    0 < p → 0 < q →
      (((p : ℝ) * ρ) • outerProduct u u =
          (ρ / (p : ℝ)) •
            outerProduct ((p : ℝ) • u) ((p : ℝ) • u)) ∧
      (((q : ℝ) * κ) • outerProduct v v =
          (κ / (q : ℝ)) •
            outerProduct ((q : ℝ) • v) ((q : ℝ) • v)) ∧
      ((-ρ) • u + ρ • u = 0) ∧
      ((-κ) • v + κ • v = 0)

/-- Nonnegative grid stresses give nonnegative condensed row and column coefficients. -/
def positivityPreservation : Prop :=
  ∀ (p q : ℕ),
    0 < p → 0 < q →
    ∀ (a b : ℕ → ℕ → ℝ)
      (ρ : InteriorRow q → ℝ) (κ : InteriorColumn p → ℝ),
      ((∀ (i j : ℕ) (hi : i < p) (hj₁ : 1 ≤ j) (hjq : j < q),
          a i j = ρ ⟨j, hj₁, hjq⟩) ∧
       (∀ (i j : ℕ) (hi₁ : 1 ≤ i) (hip : i < p) (hj : j < q),
          b i j = κ ⟨i, hi₁, hip⟩)) →
      ((∀ (i j : ℕ), i < p → j ≤ q → 0 ≤ a i j) ∧
       (∀ (i j : ℕ), i ≤ p → j < q → 0 ≤ b i j)) →
      ((∀ j : InteriorRow q,
          0 ≤ ρ j ∧ 0 ≤ ρ j / (p : ℝ)) ∧
       (∀ i : InteriorColumn p,
          0 ≤ κ i ∧ 0 ≤ κ i / (q : ℝ)))

end MathlibPlus.Open.ResearchFormalization.Grid
