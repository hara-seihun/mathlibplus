import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Quadratic

/-- The one-hole residue-avoidance set determined by the selected classes. -/
def residueAvoidanceSet (N z : ℕ) (a : ℕ → ℕ) : Set ℕ :=
  {n | n < N ∧ ∀ q : ℕ, Nat.Prime q → q ≤ z → n % q ≠ a q}

noncomputable def oddSquareImage (M : ℕ) : Finset ℕ :=
  (Finset.range (M + 1)).filter (fun x => x % 2 = 1) |>.image (fun x => x ^ 2)

/-- A selected zero class modulo two and one nonresidue class at every odd
    prime leave a large odd-square intersection. -/
def premiseMatchedOneHoleQuadraticCounterexample : Prop :=
  ∀ (N z : ℕ), ∃ a : ℕ → ℕ,
    a 2 = 0 ∧
    (∀ q : ℕ, Nat.Prime q → q % 2 = 1 → q ≤ z →
      a q < q ∧ a q ≠ 0 ∧
        ¬ ∃ y : ℕ, y ^ 2 % q = a q) ∧
    (∀ x : ℕ, x % 2 = 1 → x ^ 2 < N →
      x ^ 2 ∈ residueAvoidanceSet N z a) ∧
    let M := Nat.sqrt (N - 1)
    (∀ y : ℕ, y ∈ oddSquareImage M →
      y ∈ residueAvoidanceSet N z a) ∧
    (oddSquareImage M).card ≥ (M + 1) / 2

end MathlibPlus.Open.ResearchFormalization.Quadratic
