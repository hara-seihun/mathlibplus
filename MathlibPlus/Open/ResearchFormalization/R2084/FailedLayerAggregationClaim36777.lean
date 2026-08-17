import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2084.FailedLayerAggregationClaim36777

private def sourceThreeSunflower {α : Type*} [DecidableEq α]
    {m : ℕ} (A : Fin m → Finset α) : Prop :=
  ∃ i j k : Fin m,
    i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
    A i ∩ A j = A i ∩ A k ∧
    A i ∩ A k = A j ∩ A k

private def residualSunflower {α : Type*} [DecidableEq α]
    {m : ℕ} (R : Fin m → Finset α) : Prop :=
  ∃ C : Finset α,
    ∀ ⦃i j : Fin m⦄, i ≠ j → R i ∩ R j = C

private def residualHyperedge {α : Type*} [DecidableEq α]
    {m : ℕ} (R : Fin m → Finset α) (e : Finset (Fin m)) : Prop :=
  e.card = 3 ∧
    ∃ i j k : Fin m,
      e = {i, j, k} ∧
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      R i ∩ R j = R i ∩ R k ∧
      R i ∩ R k = R j ∩ R k

private def independentIndexSet {α : Type*} [DecidableEq α]
    {m : ℕ} (R : Fin m → Finset α) (I : Finset (Fin m)) : Prop :=
  ∀ e : Finset (Fin m), residualHyperedge R e → ¬ e ⊆ I

private def sourceDegree {α : Type*} [DecidableEq α]
    {m : ℕ} (A : Fin m → Finset α) (w : α) : ℕ :=
  (Finset.univ.filter (fun i : Fin m => w ∈ A i)).card

private def pairOccurrenceCount {α : Type*} [DecidableEq α]
    {m : ℕ} (R : Fin m → Finset α) (w : α) (i j : Fin m) : ℕ :=
  (if w ∈ R i then 1 else 0) + (if w ∈ R j then 1 else 0)

private def rankThreeMinimality : Prop :=
  (∀ r p₁ p₂ : ℕ,
    0 < p₁ → 0 < p₂ → p₁ + p₂ ≤ r → 2 * p₁ < r → 3 ≤ r) ∧
  0 < 1 ∧ 0 < 1 ∧ 1 + 1 ≤ 3 ∧ 2 * 1 < 3

/-- Claim 36777: the displayed three-member rank-three family has a first
regular layer, an independently thinned residual pair carrying a disjoint
rank-one layer, and a nonregular union on the original source family. -/
def parameterMinimalFailedLayerAggregation_claim36777 : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (u v c x y z : α),
    u ≠ v → u ≠ c → u ≠ x → u ≠ y → u ≠ z →
    v ≠ c → v ≠ x → v ≠ y → v ≠ z →
    c ≠ x → c ≠ y → c ≠ z →
    x ≠ y → x ≠ z → y ≠ z →
    let A : Fin 3 → Finset α :=
      ![{u, c, x}, {u, c, y}, {v, c, z}]
    let Y₁ : Finset α := {u, v}
    let R : Fin 3 → Finset α := fun i => A i \ Y₁
    let Y₂ : Finset α := {x, z}
    let pairIndex : Fin 2 → Fin 3 := ![0, 2]
    (∀ i : Fin 3, (A i).card = 3) ∧
      Function.Injective A ∧
      ¬ sourceThreeSunflower A ∧
      (∀ i : Fin 3, (A i ∩ Y₁).card = 1) ∧
      sourceDegree A u = 2 ∧
      sourceDegree A v = 1 ∧
      (∀ i : Fin 3,
        R i = (![ {c, x}, {c, y}, {c, z} ] : Fin 3 → Finset α) i) ∧
      residualSunflower R ∧
      residualHyperedge R {0, 1, 2} ∧
      independentIndexSet R {0, 2} ∧
      Disjoint Y₁ Y₂ ∧
      (Y₂).card = 2 ∧
      (∀ i : Fin 2, (R (pairIndex i) ∩ Y₂).card = 1) ∧
      (∀ w : α, w ∈ Y₂ → pairOccurrenceCount R w 0 2 = 1) ∧
      (A 0 ∩ (Y₁ ∪ Y₂)).card = 2 ∧
      (A 1 ∩ (Y₁ ∪ Y₂)).card = 1 ∧
      (A 2 ∩ (Y₁ ∪ Y₂)).card = 2 ∧
      (∀ {m : ℕ} (R' : Fin m → Finset α)
        (e : Finset (Fin m)), residualHyperedge R' e → 3 ≤ m) ∧
      rankThreeMinimality

end MathlibPlus.Open.ResearchFormalization.R2084.FailedLayerAggregationClaim36777
