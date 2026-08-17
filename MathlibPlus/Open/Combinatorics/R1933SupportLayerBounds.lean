import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Combinatorics.R1933

private noncomputable def literalSupport {α : Type*} {m : ℕ}
    [DecidableEq α] (F : Fin m → Finset α) (x : α) : Finset (Fin m) :=
  (Finset.univ : Finset (Fin m)).filter (fun i => x ∈ F i)

private noncomputable def groundCarrier {α : Type*} {m : ℕ}
    [DecidableEq α] (F : Fin m → Finset α) : Finset α :=
  (Finset.univ : Finset (Fin m)).biUnion F

private def uniformDistinct {α : Type*} {m : ℕ}
    [DecidableEq α] (n : ℕ) (F : Fin m → Finset α) : Prop :=
  (∀ i, (F i).card = n) ∧ Function.Injective F

private noncomputable def supportPatterns {α : Type*} {m : ℕ}
    [DecidableEq α] (F : Fin m → Finset α) : Finset (Finset (Fin m)) :=
  (groundCarrier F).image (literalSupport F)

private def laminarPatterns {α : Type*} {m : ℕ}
    [DecidableEq α] (F : Fin m → Finset α)
    (L : Finset (Finset (Fin m))) : Prop :=
  ∀ S ∈ L, ∀ T ∈ L,
    S ⊆ T ∨ T ⊆ S ∨ Disjoint S T

private def singletonCompatible {m : ℕ}
    (L : Finset (Finset (Fin m))) : Prop :=
  ∀ S, S.card = 1 → ∀ T ∈ L,
    S ⊆ T ∨ T ⊆ S ∨ Disjoint S T

private def noSunflower {α : Type*} {m n q : ℕ}
    [DecidableEq α] (F : Fin m → Finset α) : Prop :=
  ∀ I : Finset (Fin m), I.card = q + 1 →
    ¬ ∃ C : Finset α,
      ∀ i ∈ I, ∀ j ∈ I, i ≠ j → F i ∩ F j = C

private def matchingNumberAtMost {α : Type*} {m ν : ℕ}
    [DecidableEq α] (F : Fin m → Finset α) : Prop :=
  ∀ I : Finset (Fin m),
    (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (F i) (F j)) → I.card ≤ ν

private def boundedLayerColoring {α : Type*} {m n D q : ℕ}
    [DecidableEq α] (F : Fin m → Finset α)
    (B : Finset (Finset (Fin m))) : Prop :=
  ∃ color : Fin m → Fin (1 + (D - 1) * n),
    ∀ c : Fin (1 + (D - 1) * n), ∀ S ∈ B,
      ((Finset.univ : Finset (Fin m)).filter (fun i => color i = c) ∩ S).card ≤ 1

private def layeredSupportHypotheses {α : Type*}
    [DecidableEq α] (m n D q ν : ℕ)
    (F : Fin m → Finset α)
    (L B : Finset (Finset (Fin m))) : Prop :=
  uniformDistinct n F ∧
    2 ≤ q ∧
    noSunflower (n := n) (q := q) F ∧
    matchingNumberAtMost (ν := ν) F ∧
    supportPatterns F = L ∪ B ∧
    Disjoint L B ∧
    laminarPatterns F L ∧
    singletonCompatible L ∧
    (∀ S ∈ B, S.card ≤ D) ∧
    boundedLayerColoring (n := n) (D := D) (q := q) F B

private def colorClassSize {m r : ℕ} (color : Fin m → Fin r) (c : Fin r) : ℕ :=
  ((Finset.univ : Finset (Fin m)).filter (fun i => color i = c)).card

/-- Claim 36334: the literal bounded-support conflict layer admits the exact
`1+(D-1)n` color decomposition, each color class has the q-ary laminar bound,
and the two displayed family bounds follow with matching number ν. -/
def boundedLayerFixedBaseBound_claim36334 : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (m n D q ν : ℕ) (F : Fin m → Finset α)
    (L B : Finset (Finset (Fin m))),
    layeredSupportHypotheses m n D q ν F L B →
      ∃ color : Fin m → Fin (1 + (D - 1) * n),
        (∀ c, colorClassSize color c ≤ q ^ n) ∧
          m ≤ (1 + (D - 1) * n) * q ^ n ∧
          m ≤ (1 + (D - 1) * n) * ν * q ^ (n - 1) ∧
          1 + (D - 1) * n ≤ D ^ n ∧
          m ≤ (D * q) ^ n

/-- Claim 36335: the pairwise-intersecting k=3, D=2 specialization of the
same literal support carrier gives the stated `(n+1)2^(n-1)` and `4^n` bounds. -/
def pairwiseIntersectingDegreeTwoBound_claim36335 : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (m n : ℕ) (F : Fin m → Finset α)
    (L B : Finset (Finset (Fin m))),
    layeredSupportHypotheses m n 2 2 1 F L B →
      (∀ i : Fin m, ∀ j : Fin m, i ≠ j →
        (F i ∩ F j).Nonempty) →
        m ≤ (n + 1) * 2 ^ (n - 1) ∧
          (n + 1) * 2 ^ (n - 1) ≤ 4 ^ n

end MathlibPlus.Open.Combinatorics.R1933
