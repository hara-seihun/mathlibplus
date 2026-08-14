import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

open scoped BigOperators

/-- The number of coordinates of `A` whose degree is at most the `j`th profile level. -/
def profileCount {ι : Type} [DecidableEq ι]
    (A : Finset ι) (d : ι → ℕ) (S j : ℕ) : ℕ :=
  (A.filter (fun x => d x ≤ S ^ j)).card

/-- The `j`th degree order statistic, with the harmless out-of-range default 0. -/
def degreeOrderStatistic {ι : Type} [DecidableEq ι]
    (A : Finset ι) (d : ι → ℕ) (j : ℕ) : ℕ :=
  (Multiset.sort (A.val.map d)).getD (j - 1) 0

/-- The profile-good condition `q_j(A) ≥ j` for some `1 ≤ j ≤ r`. -/
def profileGood {ι : Type} [DecidableEq ι]
    (A : Finset ι) (d : ι → ℕ) (S r : ℕ) : Prop :=
  ∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ j ≤ profileCount A d S j

/--
The exact complementary high-degree profile from Claim 36887.  The finite
coordinate set is kept explicit: `A` is the member and `d` its coordinate
degree function.  The first conjunct is the order-statistic equivalence;
the second records the stated maximum-degree and degree-sum consequences.
-/
def exactComplementaryHighDegreeProfile : Prop :=
  ∀ {ι : Type} [DecidableEq ι] (r S : ℕ)
    (F : Set (Finset ι)) (d : ι → ℕ),
    1 ≤ r → 1 ≤ S →
      (∀ A ∈ F, A.card = r) →
        (∀ A : Finset ι, A.card = r →
          ((¬ profileGood A d S r) ↔
            ∀ j : ℕ, 1 ≤ j → j ≤ r →
              degreeOrderStatistic A d j > S ^ j)) ∧
        ((¬ ∀ A ∈ F, profileGood A d S r) →
          ∃ A ∈ F,
            (∀ j : ℕ, 1 ≤ j → j ≤ r →
              degreeOrderStatistic A d j > S ^ j) ∧
            (Finset.sup A d > S ^ r) ∧
            ((∑ x ∈ A, d x) > (∑ j ∈ Finset.Icc 1 r, S ^ j)))

end MathlibPlus.Open.ResearchFormalization
