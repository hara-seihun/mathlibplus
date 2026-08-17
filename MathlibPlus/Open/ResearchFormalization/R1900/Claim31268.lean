import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1900.Claim31268

noncomputable section

open scoped BigOperators

/-- A sunflower is expressed by the common pairwise intersection of its
members.  The family is a `Finset`, so its members are distinct. -/
def isKSunflower {α : Type*} [DecidableEq α]
    (I : Finset (Finset α)) : Prop :=
  ∃ C : Finset α,
    ∀ ⦃B⦄, B ∈ I → ∀ ⦃D⦄, D ∈ I → B ≠ D → B ∩ D = C

/-- The exact finite-family form of being `k`-sunflower-free. -/
def kSunflowerFree {α : Type*} [DecidableEq α]
    (k : ℕ) (G : Finset (Finset α)) : Prop :=
  ∀ I : Finset (Finset α), I.card = k → I ⊆ G → ¬ isKSunflower I

/-- No `k-1` members are pairwise disjoint, i.e. the matching number is at
most `k-2`. -/
def matchingAtMost {α : Type*} [DecidableEq α]
    (k : ℕ) (G : Finset (Finset α)) : Prop :=
  ∀ I : Finset (Finset α), I.card = k - 1 → I ⊆ G →
    ¬ ∀ ⦃B⦄, B ∈ I → ∀ ⦃D⦄, D ∈ I → B ≠ D → Disjoint B D

/-- The finite carrier for a distinct uniform family with the bounded-matching
hypothesis used by the admitted trace statement. -/
def boundedMatchingSunflowerFamily {α : Type*} [DecidableEq α]
    (r k : ℕ) (G : Finset (Finset α)) : Prop :=
  (∀ B ∈ G, B.card = r) ∧
    kSunflowerFree k G ∧
      matchingAtMost k G

/-- The set of occupied exact values `A ∩ B`; `Finset.image` removes member
occurrence multiplicity. -/
def occupiedExactTraces {α : Type*} [DecidableEq α]
    (A : Finset α) (G : Finset (Finset α)) : Finset (Finset α) :=
  G.image (fun B => A ∩ B)

/-- The Kraft-weighted sum over distinct occupied exact traces. -/
def kraftTracePartitionFunction {α : Type*} [DecidableEq α]
    (K : ℝ) (A : Finset α) (G : Finset (Finset α)) : ℝ :=
  ∑ T ∈ occupiedExactTraces A G, (K⁻¹ : ℝ) ^ T.card

/-- The `K`-Kraft-good predicate from the admitted statement. -/
def isKraftGood {α : Type*} [DecidableEq α]
    (K : ℝ) (A : Finset α) (G : Finset (Finset α)) : Prop :=
  kraftTracePartitionFunction K A G ≤ 1

/-- Claim 31268: for an actual pivot in the exact distinct uniform bounded-
matching family, the Kraft sum is indexed by distinct occupied trace values,
and Kraft-goodness is exactly the inequality `Z_K ≤ 1`. -/
def claim31268 : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α]
    (r k : ℕ) (G : Finset (Finset α)) (A : Finset α) (K : ℝ),
    3 ≤ k →
      0 < r →
        boundedMatchingSunflowerFamily r k G →
          A ∈ G →
            1 < K →
              let T := occupiedExactTraces A G
              let Z := ∑ U ∈ T, (K⁻¹ : ℝ) ^ U.card
              T = G.image (fun B => A ∩ B) ∧
                kraftTracePartitionFunction K A G = Z ∧
                  (isKraftGood K A G ↔ Z ≤ 1)

end

end MathlibPlus.Open.ResearchFormalization.R1900.Claim31268
