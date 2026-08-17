import Mathlib
import MathlibPlus.Combinatorics.Claim36143

namespace MathlibPlus.Open.ShearFamilyBatch

noncomputable section

abbrev claim36145_Point := MathlibPlus.Combinatorics.Point_claim36143
abbrev claim36145_Length (k : ℕ) := MathlibPlus.Combinatorics.hingedL_claim36143 k

def claim36145_openBox (k : ℕ) (a : Fin k → ℝ) : Prop :=
  ∀ r : Fin k, (1 : ℝ) / 10 < a r ∧ a r < 1 / 5

def claim36145_distance (x y : claim36145_Point) : ℝ :=
  Real.sqrt ((x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2)

def claim36145_configuration (k : ℕ) (a : Fin k → ℝ) :
    Finset claim36145_Point :=
  MathlibPlus.Combinatorics.hingedConfiguration_claim36143 k a

def claim36145_minimumDistanceOne (k : ℕ) (a : Fin k → ℝ) : Prop :=
  (∀ x ∈ claim36145_configuration k a,
    ∀ y ∈ claim36145_configuration k a, x ≠ y →
      1 ≤ claim36145_distance x y) ∧
  ∃ x ∈ claim36145_configuration k a,
    ∃ y ∈ claim36145_configuration k a,
      x ≠ y ∧ claim36145_distance x y = 1

def claim36145_diameterLength (k : ℕ) (a : Fin k → ℝ) : Prop :=
  (∀ x ∈ claim36145_configuration k a,
    ∀ y ∈ claim36145_configuration k a,
      claim36145_distance x y ≤ (claim36145_Length k : ℝ)) ∧
  claim36145_distance
      (MathlibPlus.Combinatorics.basePoint_claim36143 (0 : Fin (claim36145_Length k + 1)))
      (MathlibPlus.Combinatorics.basePoint_claim36143
        (Fin.last (claim36145_Length k))) =
    (claim36145_Length k : ℝ)

def claim36145_topInteriorBounds (k : ℕ) (a : Fin k → ℝ) : Prop :=
  ∀ r : Fin k,
    2 < (MathlibPlus.Combinatorics.upperPoint_claim36143 a r 0).1 ∧
      (MathlibPlus.Combinatorics.upperPoint_claim36143 a r 0).1 <
        (claim36145_Length k : ℝ) - 4 ∧
      0 < (MathlibPlus.Combinatorics.upperPoint_claim36143 a r 0).2 ∧
      (MathlibPlus.Combinatorics.upperPoint_claim36143 a r 0).2 < 1 ∧
    2 < (MathlibPlus.Combinatorics.upperPoint_claim36143 a r 1).1 ∧
      (MathlibPlus.Combinatorics.upperPoint_claim36143 a r 1).1 <
        (claim36145_Length k : ℝ) - 4 ∧
      0 < (MathlibPlus.Combinatorics.upperPoint_claim36143 a r 1).2 ∧
      (MathlibPlus.Combinatorics.upperPoint_claim36143 a r 1).2 < 1

def claim36145_topDistancesBelowDiameter (k : ℕ) (a : Fin k → ℝ) : Prop :=
  (∀ r : Fin k, ∀ t : Fin (claim36145_Length k + 1),
    claim36145_distance
        (MathlibPlus.Combinatorics.upperPoint_claim36143 a r 0)
        (MathlibPlus.Combinatorics.basePoint_claim36143 t) <
      (claim36145_Length k : ℝ) ∧
    claim36145_distance
        (MathlibPlus.Combinatorics.upperPoint_claim36143 a r 1)
        (MathlibPlus.Combinatorics.basePoint_claim36143 t) <
      (claim36145_Length k : ℝ)) ∧
  (∀ r s : Fin k, ∀ b c : Fin 2,
    claim36145_distance
        (MathlibPlus.Combinatorics.upperPoint_claim36143 a r b)
        (MathlibPlus.Combinatorics.upperPoint_claim36143 a s c) <
      (claim36145_Length k : ℝ))

def fixedMinimumDistanceAndDiameter : Prop :=
  ∀ (k : ℕ), 1 ≤ k →
    ∀ (a : Fin k → ℝ), claim36145_openBox k a →
      claim36145_minimumDistanceOne k a ∧
      claim36145_diameterLength k a ∧
      claim36145_topInteriorBounds k a ∧
      claim36145_topDistancesBelowDiameter k a

end

end MathlibPlus.Open.ShearFamilyBatch
