import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch_01a003d0_6085_7e88_9855_ed1ff0b1b6e8

open scoped BigOperators
open BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Q0056Claim16294

noncomputable section

open MathlibPlus.Open.ResearchFormalizationBatch_01a003d0_6085_7e88_9855_ed1ff0b1b6e8

/-- The finite set of nonempty incidence supports realized by an indexed family. -/
def supportPatterns {α : Type*} [DecidableEq α] {m : ℕ}
    (A : Fin m → Finset α) : Finset (Finset (Fin m)) :=
  (indexedGround A).image (incidenceSupport A)

/-- Laminarity allows nesting or disjointness, not only total nesting. -/
def laminarSupportFamily {m : ℕ}
    (L : Finset (Finset (Fin m))) : Prop :=
  ∀ ⦃S T : Finset (Fin m)⦄, S ∈ L → T ∈ L →
    S.Nonempty → T.Nonempty →
      S ⊆ T ∨ T ⊆ S ∨ Disjoint S T

/-- A support layer is closed under unions of its members. -/
def unionClosedSupportLayer {m : ℕ}
    (U : Finset (Finset (Fin m))) : Prop :=
  ∀ ⦃S T : Finset (Fin m)⦄, S ∈ U → T ∈ U → S ∪ T ∈ U

/-- A faithful D=1 hybrid decomposition: `P` is the full complement of the
laminar backbone, and it is partitioned into union-closed layers and exceptions. -/
def hybridSupportDecomposition {α : Type*} [DecidableEq α]
    {m c e : ℕ} (A : Fin m → Finset α)
    (L : Finset (Finset (Fin m)))
    (layers : Fin c → Finset (Finset (Fin m)))
    (E P : Finset (Finset (Fin m))) : Prop :=
  laminarSupportFamily L ∧
    (∀ j : Fin c,
      unionClosedSupportLayer (layers j) ∧
        (∀ S ∈ layers j, S ∈ P)) ∧
    (∀ j₁ j₂ : Fin c, j₁ ≠ j₂ → Disjoint (layers j₁) (layers j₂)) ∧
    (∀ S ∈ E, S ∈ P) ∧
    (∀ S ∈ E, ∀ j : Fin c, S ∉ layers j) ∧
    E.card = e ∧
    Disjoint L P ∧
    (∀ S, S ∈ supportPatterns A ↔ S ∈ L ∨ S ∈ P) ∧
    (∀ S, S ∈ P ↔ S ∈ E ∨ ∃ j : Fin c, S ∈ layers j) ∧
    (∀ S ∈ P, S.Nonempty ∧ 0 < supportMultiplicity A S)

/-- The union-closed frequency constant used by the hybrid bound. -/
def unionClosedFrequencyConstant : ℝ :=
  (3 - Real.sqrt 5) / 2

/-- The explicit base in the `k = 3`, one-layer, no-exception case. -/
def explicitHybridBase : ℝ :=
  2 * Real.rpow (3 / 2 : ℝ) ((3 + Real.sqrt 5) / 2)

/-- The displayed decimal is retained as a genuine numerical approximation. -/
def explicitHybridBaseApproximation : Prop :=
  |explicitHybridBase - (57815315 : ℝ) / 10000000| < (1 : ℝ) / 10000000

/-- Laminar backbone plus union-closed layers, with the complete nonlaminar
support product and its exponential/base consequences. -/
def laminarBackbone_unionClosedLayers_16294 : Prop :=
  ∀ (α : Type*) [DecidableEq α] (m n k q c e : ℕ) (β : ℝ)
    (A : Fin m → Finset α)
    (L : Finset (Finset (Fin m)))
    (layers : Fin c → Finset (Finset (Fin m)))
    (E P : Finset (Finset (Fin m))),
    2 ≤ k →
      q = k - 1 →
      (∀ i, (A i).card = n) →
      Function.Injective A →
      hybridSupportDecomposition (e := e) A L layers E P →
      (m : ℝ) ≤
        (q : ℝ) ^ n *
          ∏ S ∈ P,
            (1 + (q : ℝ) ^ (-(supportMultiplicity A S : ℤ))) ∧
      (m : ℝ) ≤
        (q : ℝ) ^ n *
          Real.rpow
            (1 + (q : ℝ)⁻¹)
            ((e : ℝ) + (c : ℝ) * unionClosedFrequencyConstant⁻¹ * (n : ℝ)) ∧
      ((e : ℝ) ≤ β * (n : ℝ) →
        (m : ℝ) ≤
          ((q : ℝ) *
              Real.rpow
                (1 + (q : ℝ)⁻¹)
                (β + (c : ℝ) * unionClosedFrequencyConstant⁻¹)) ^ n) ∧
      (k = 3 → c = 1 → e = 0 → explicitHybridBaseApproximation)

end
end MathlibPlus.Open.ResearchFormalization.Q0056Claim16294
