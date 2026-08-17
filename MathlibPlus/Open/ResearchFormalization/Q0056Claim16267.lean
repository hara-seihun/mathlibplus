import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch_01a003d0_6085_7e88_9855_ed1ff0b1b6e8

open scoped BigOperators
open Filter Topology

namespace MathlibPlus.Open.ResearchFormalization.Q0056Claim16267

noncomputable section

/-- Fractional support multiplicities, with zero mass on the empty support and
the exact-two/exact-one cover constraints. -/
def fractionalSupportCover (m : ℕ) (w : Finset (Fin m) → ℝ) : Prop :=
  (∀ S : Finset (Fin m), S.Nonempty → 0 ≤ w S) ∧
    w ∅ = 0 ∧
    (∀ I : Finset (Fin m), I.card = 3 →
      1 ≤ ∑ S : Finset (Fin m),
        if (S ∩ I).card = 2 then w S else 0) ∧
    (∀ i j : Fin m, i ≠ j →
      1 ≤ ∑ S : Finset (Fin m),
        if (S ∩ {i, j}).card = 1 then w S else 0)

/-- The maximum member load of a fractional support cover at a member. -/
def fractionalSupportLoad (m : ℕ) (w : Finset (Fin m) → ℝ) (i : Fin m) : ℝ :=
  ∑ S : Finset (Fin m), if i ∈ S then w S else 0

/-- The exact value asserted for the fractional optimum. -/
def fractionalSupportCoverValue (m : ℕ) : ℝ :=
  (((m - 1 : ℕ) : ℝ) * ((m - 2 : ℕ) : ℝ)) /
    (3 * (((m - 1 : ℕ) ^ 2 / 4 : ℕ) : ℝ))

/-- The equal weight assigned to every support of the balanced size. -/
def balancedFractionalSupportWeight (m : ℕ) (S : Finset (Fin m)) : ℝ :=
  let s := 1 + (m - 1) / 2
  if S.card = s then
    1 / (3 * (Nat.choose (m - 3) (s - 2) : ℝ))
  else 0

/-- Exact fractional support-cover optimum, including the balanced equality
weights, tight triple constraints, separated pairs, and the limit `4/3`. -/
def exactFractionalSupportCoverOptimum_16267 : Prop :=
  (∀ m : ℕ, 4 ≤ m →
    (∀ w : Finset (Fin m) → ℝ,
      fractionalSupportCover m w →
        ∃ i : Fin m,
          fractionalSupportCoverValue m ≤ fractionalSupportLoad m w i) ∧
    ∃ w : Finset (Fin m) → ℝ,
      fractionalSupportCover m w ∧
        (∀ i : Fin m,
          fractionalSupportLoad m w i = fractionalSupportCoverValue m) ∧
        (∀ S : Finset (Fin m),
          w S = balancedFractionalSupportWeight m S) ∧
        (∀ I : Finset (Fin m), I.card = 3 →
          (∑ S : Finset (Fin m),
            if (S ∩ I).card = 2 then w S else 0) = 1) ∧
        (∀ i j : Fin m, i ≠ j →
          1 ≤ ∑ S : Finset (Fin m),
            if (S ∩ {i, j}).card = 1 then w S else 0)) ∧
  Tendsto (fun m : ℕ => fractionalSupportCoverValue m) atTop
    (𝓝 ((4 : ℝ) / 3))

end
end MathlibPlus.Open.ResearchFormalization.Q0056Claim16267
