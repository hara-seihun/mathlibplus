import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch_01a003d0_6085_7e88_9855_ed1ff0b1b6e8

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Q0056Claim16275

open MathlibPlus.Open.ResearchFormalizationBatch_01a003d0_6085_7e88_9855_ed1ff0b1b6e8

noncomputable section

/-- A finite family is uniform, three-sunflower-free, and has pairwise
intersection size at most `t` for distinct members. -/
def boundedIntersectionFamily {α : Type*} [DecidableEq α]
    (n t : ℕ) (F : Finset (Finset α)) : Prop :=
  isUniformFamily F n ∧
    isSunflowerFreeFamily F 3 ∧
    (∀ A ∈ F, ∀ B ∈ F, A ≠ B → (A ∩ B).card ≤ t)

/-- `M(n,t)` is represented by an attained universal maximum over finite
set-family carriers. -/
def isBoundedIntersectionMaximum (n t M : ℕ) : Prop :=
  (∃ g : ℕ, ∃ F : Finset (Finset (Fin g)),
    F.card = M ∧ boundedIntersectionFamily n t F) ∧
  (∀ (g : ℕ) (F : Finset (Finset (Fin g))),
    boundedIntersectionFamily n t F → F.card ≤ M)

/-- The bounded-intersection recursion and the `t = 0` base bound. -/
def boundedIntersectionRecursion_16275 : Prop :=
  (∀ n : ℕ, ∀ M : ℕ,
    isBoundedIntersectionMaximum n 0 M → M ≤ 2) ∧
  (∀ (n t M M' : ℕ),
    isBoundedIntersectionMaximum n t M →
    isBoundedIntersectionMaximum (n - 1) (t - 1) M' →
      M ≤ 1 + n *
        (∑ j ∈ Finset.range (t + 1), Nat.choose n j) * M')

end
end MathlibPlus.Open.ResearchFormalization.Q0056Claim16275
