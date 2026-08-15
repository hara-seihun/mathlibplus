import Mathlib

namespace MathlibPlus.Open.FormalizationBatch

noncomputable def reflectedCoefficient (i n : ℕ) : ℝ :=
  if i ≤ n then
    (Real.Gamma (2 * (i : ℝ) + (5 / 2 : ℝ)) /
      Real.Gamma ((n : ℝ) + (3 / 2 : ℝ))) *
      (Nat.choose (i + 1) (n - i) : ℝ)
  else 0

noncomputable def reflectedCoefficientMinor (r : ℕ) (n : Fin r → ℕ) : ℝ :=
  Matrix.det (fun (i j : Fin r) => reflectedCoefficient i.1 (n j))

def staircasePartition (r : ℕ) (part : Fin r → ℕ) : Prop :=
  (∀ ⦃i j : Fin r⦄, i ≤ j → part j ≤ part i) ∧
    (∀ i : Fin r, part i ≤ r - i.1)

def staircaseDegreeSet (r : ℕ) (n : Fin r → ℕ) : Prop :=
  ∃ part : Fin r → ℕ,
    staircasePartition r part ∧
      ∀ j : Fin r, n j = j.1 + part (Fin.rev j)

def nonzeroMaximalMinorSupport : Prop :=
  ∀ (r : ℕ) (n : Fin r → ℕ),
    StrictMono n →
      (reflectedCoefficientMinor r n ≠ 0 ↔
          ∀ j : Fin r, n j ≤ 2 * j.1 + 1) ∧
        (reflectedCoefficientMinor r n ≠ 0 ↔ staircaseDegreeSet r n)

end MathlibPlus.Open.FormalizationBatch
