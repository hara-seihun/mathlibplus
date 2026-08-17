import Mathlib
import MathlibPlus.Open.Combinatorics.AdmittedClaims36875_36918
import MathlibPlus.Open.ResearchFormalizationBatch_01a003cb_d995_7564_b82d_d782ff7e0528

namespace MathlibPlus.Open.Combinatorics.Retry36884

private def regularLayer
    {α : Type*} [DecidableEq α] (m r k p s : ℕ)
    (A : Fin m → Finset α) (Y : Finset α) : Prop :=
  3 ≤ k ∧
  Function.Injective A ∧
  (∀ i : Fin m, (A i).card = r) ∧
  (¬ MathlibPlus.Open.ResearchFormalizationBatch.isKSunflower k
      (Finset.univ.image A)) ∧
  (∀ i : Fin m, (A i ∩ Y).card = p) ∧
  (∀ y ∈ Y,
    (Finset.univ.filter (fun i : Fin m => y ∈ A i)).card ≤ s)

private def residualUpperBound
    {α : Type*} [DecidableEq α]
    (k : ℕ) (F : ℕ → ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (G : Finset (Finset α)),
    (∀ B ∈ G, B.card = n) →
    ¬ MathlibPlus.Open.ResearchFormalizationBatch.isKSunflower k G →
    G.card ≤ F k n

private def indexedFamily
    {α : Type*} [DecidableEq α]
    (m : ℕ) (A : Fin m → Finset α) : Finset (Finset α) :=
  Finset.univ.image A

/-- Exact transfer from a regular literal layer to its distinct residual family. -/
def claim36884 : Prop :=
  ∀ (α : Type*) [DecidableEq α]
    (m r k p s : ℕ)
    (A : Fin m → Finset α) (Y : Finset α)
    (F : ℕ → ℕ → ℕ),
    regularLayer m r k p s A Y →
    residualUpperBound (α := α) k F →
    m ≤ (k - 1) * (1 + p * (s - 1)) * F k (r - p) ∧
    (k = 3 →
      m ≤ 2 * (1 + p * (s - 1)) * F 3 (r - p)) ∧
    (∀ Δ : ℕ,
      Y = MathlibPlus.Open.ResearchFormalizationBatch.groundCoordinates
        (indexedFamily (α := α) m A) →
      p = r →
      (∀ y ∈ Y,
        (Finset.univ.filter (fun i : Fin m => y ∈ A i)).card ≤ Δ) →
      m ≤ (k - 1) * (1 + r * (Δ - 1)))

end MathlibPlus.Open.Combinatorics.Retry36884
