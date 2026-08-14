import Mathlib

open Filter

namespace MathlibPlus.Open.Combinatorics

/-- Claim 36875: the combined closest/farthest active graph of a finite planar
configuration is the graph whose edges are precisely the pairs at the minimum
or maximum pairwise distance. -/
def combinedClosestFarthestActiveGraph_claim36875 : Prop :=
  ∀ (n : ℕ), 3 ≤ n →
    ∀ (X : Fin n → EuclideanSpace ℝ (Fin 2)),
      Function.Injective X →
      let distances : Set ℝ :=
        {d | ∃ i j : Fin n, i < j ∧ d = dist (X i) (X j)}
      let δ : ℝ := sInf distances
      let D : ℝ := sSup distances
      ∃ A : SimpleGraph (Fin n),
        ∀ i j : Fin n,
          A.Adj i j ↔
            i ≠ j ∧
              (dist (X i) (X j) = δ ∨ dist (X i) (X j) = D)

/-- Claim 36881: a distinct uniform sunflower-free family together with a
literal regular layer, its indexed traces, and its indexed residual
occurrences. -/
def regularLiteralLayerAndIndexedTraces_claim36881 : Prop :=
  ∀ (α : Type*) [DecidableEq α]
    (m r k p s : ℕ) (A : Fin m → Finset α) (Y : Finset α),
    3 ≤ k →
    Function.Injective A →
    (∀ i : Fin m, (A i).card = r) →
    (∀ S : Finset (Fin m), S.card = k →
      ¬ ∃ C : Finset α,
        (∀ i ∈ S, C ⊆ A i) ∧
        (∀ i ∈ S, ∀ j ∈ S, i ≠ j →
          Disjoint (A i \ C) (A j \ C))) →
    (∀ i : Fin m, (A i ∩ Y).card = p) →
    (∀ y ∈ Y,
      (Finset.univ.filter (fun i : Fin m => y ∈ A i)).card ≤ s) →
    let T : Fin m → Finset α := fun i => A i ∩ Y
    let B : Fin m → Finset α := fun i => A i \ Y
    (∀ i : Fin m, T i = A i ∩ Y) ∧
      (∀ i : Fin m, B i = A i \ Y) ∧
      (∀ i : Fin m, (T i).card = p) ∧
      (∀ i : Fin m, Disjoint (T i) (B i))

/-- Claim 36883: after pairwise-disjoint indexed trace matching, the residual
occurrences remain sunflower-free; no residual set has multiplicity k, and the
ordinary distinct residual family has multiplicity at most k-1. -/
def residualSunflowerFidelityAndMultiplicity_claim36883 : Prop :=
  ∀ (α : Type*) [DecidableEq α]
    (m r k p : ℕ) (A : Fin m → Finset α) (Y : Finset α)
    (I : Finset (Fin m)),
    3 ≤ k →
    Function.Injective A →
    (∀ i : Fin m, (A i).card = r) →
    (∀ S : Finset (Fin m), S.card = k →
      ¬ ∃ C : Finset α,
        (∀ i ∈ S, C ⊆ A i) ∧
        (∀ i ∈ S, ∀ j ∈ S, i ≠ j →
          Disjoint (A i \ C) (A j \ C))) →
    (∀ i ∈ I, (A i ∩ Y).card = p) →
    (∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint (A i ∩ Y) (A j ∩ Y)) →
    let B : Fin m → Finset α := fun i => A i \ Y
    let R : Finset (Finset α) :=
      (Finset.univ.filter (fun i : Fin m => i ∈ I)).image B
    (¬ ∃ S : Finset (Fin m),
        S ⊆ I ∧ S.card = k ∧
          ∃ C : Finset α,
            (∀ i ∈ S, C ⊆ B i) ∧
            (∀ i ∈ S, ∀ j ∈ S, i ≠ j →
              Disjoint (B i \ C) (B j \ C))) ∧
      (∀ Q : Finset α,
        (Finset.univ.filter (fun i : Fin m => i ∈ I ∧ B i = Q)).card ≤ k - 1) ∧
      (∀ S : Finset (Finset α), S ⊆ R → S.card = k →
        ¬ ∃ C : Finset α,
          (∀ Q ∈ S, C ⊆ Q) ∧
          (∀ Q ∈ S, ∀ Q' ∈ S, Q ≠ Q' →
            Disjoint (Q \ C) (Q' \ C)))

/-- Claim 36889: a cap-only scalar induction has a full-rank coefficient that
is eventually larger than one, with the stated asymptotic slope. -/
def scalarLinkCapSelfBootstrapObstruction_claim36889 : Prop :=
  ∀ (k B : ℕ), 3 ≤ k → 1 < B →
    ∀ (τ : ℕ → ℕ),
      (∀ r : ℕ, B ^ (r - 1) ≤ τ r) →
      let Γ : ℕ → ℝ := fun r =>
        (k - 1 : ℝ) *
          (1 + (r : ℝ) * ((B : ℝ) ^ (r - 1) - 1)) /
            (B : ℝ) ^ r
      (¬ ∀ r : ℕ, Γ r ≤ 1) ∧
        (∀ N : ℕ, ∃ r : ℕ, N ≤ r ∧ 1 < Γ r) ∧
        Tendsto (fun r : ℕ => Γ r / (r : ℝ)) atTop
          (nhds ((k - 1 : ℝ) / B))

/-- Claim 36890: the direct product of the four C4 edges has the exact
base-two size, rank, coordinate degrees, threshold placement, and Record-4
loss. -/
def sharpOrdinaryBaseTwoC4ProductFixture_claim36890 : Prop :=
  ∀ (g : ℕ), 1 ≤ g →
    let E : Fin 4 → Finset (Fin 4) := fun q =>
      if q = 0 then {0, 1} else
      if q = 1 then {1, 2} else
      if q = 2 then {2, 3} else {3, 0}
    let P : (Fin g → Fin 4) → Finset (Fin g × Fin 4) := fun a =>
      Finset.univ.biUnion (fun t =>
        (E (a t)).image (fun v => (t, v)))
    let 𝓕 : Finset (Finset (Fin g × Fin 4)) :=
      (Finset.univ : Finset (Fin g → Fin 4)).image P
    let r : ℕ := 2 * g
    let deg : Fin g × Fin 4 → ℕ := fun q =>
      ((Finset.univ : Finset (Fin g → Fin 4)).filter
        (fun a => q.2 ∈ E (a q.1))).card
    (∀ a, (P a).card = r) ∧
      Function.Injective P ∧
      𝓕.card = 4 ^ g ∧
      (∀ S : Finset (Fin g → Fin 4), S.card = 3 →
        ¬ ∃ C : Finset (Fin g × Fin 4),
          (∀ a ∈ S, C ⊆ P a) ∧
          (∀ a ∈ S, ∀ b ∈ S, a ≠ b →
            Disjoint (P a \ C) (P b \ C))) ∧
      (∀ q, deg q = 2 * 4 ^ (g - 1)) ∧
      (∀ (τ : ℕ → ℕ),
        (∀ j < r, τ j < 2 ^ (r - 1)) →
        τ r = 2 ^ (r - 1) →
        ∀ a,
          (∀ q ∈ P a, τ r ≥ deg q) ∧
          (∀ j < r, ∀ q ∈ P a, τ j < deg q)) ∧
      ((2 ^ r : ℚ) = 4 ^ g) ∧
      ((2 : ℚ) *
          (1 + (r : ℚ) * ((2 : ℚ) ^ (r - 1) - 1)) /
            (2 : ℚ) ^ r =
        (r : ℚ) - (r - 1 : ℚ) / (2 : ℚ) ^ (r - 1))

end MathlibPlus.Open.Combinatorics
