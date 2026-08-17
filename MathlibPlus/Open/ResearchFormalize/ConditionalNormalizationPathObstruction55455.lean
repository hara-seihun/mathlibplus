import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalize

/-- The directed incidence of weighted edges on a finite oriented path. -/
def realPathIncidence {V : Type*} [DecidableEq V] {ℓ : ℕ}
    (P : Fin (ℓ + 1) → V) (w : Fin ℓ → ℝ) : V → ℝ :=
  fun v => ∑ i : Fin ℓ,
    if v = P (Fin.castSucc i) then w i
    else if v = P (Fin.succ i) then -w i
    else 0

/-- The unit endpoint boundary of the oriented path. -/
def realPathEndpointBoundary {V : Type*} [DecidableEq V] {ℓ : ℕ}
    (P : Fin (ℓ + 1) → V) : V → ℝ :=
  fun v =>
    if v = P 0 then 1
    else if v = P (Fin.last ℓ) then -1
    else 0

/-- A concrete same-path, nonnegative, proper-support repair predicate. -/
def samePathLocalizedNonnegativeRepair {V : Type*} [DecidableEq V]
    {ℓ : ℕ} (P : Fin (ℓ + 1) → V) (q r : Fin ℓ → ℝ) : Prop :=
  (∀ i, 0 ≤ q i) ∧
    (∀ i, 0 ≤ r i) ∧
    (∃ i, q i ≠ 0) ∧
    (∃ i, q i = 0) ∧
    realPathIncidence P (fun i => q i + r i) =
      realPathEndpointBoundary P ∧
    (∃ i, q i + r i = 0)

/--
R-4922.6: a proper-support nonnegative component of a unit path decomposition
cannot be repaired locally on that same path at the original endpoint scale.
Every feasible same-path repair is the unique coordinate complement, so its
sum with the selected component is the full unit telescope.  Thus the final
negation rules out the genuinely localized same-path/nonnegative branch; an
unmodeled repair must leave that branch (for example by using an off-path
route or by leaving the nonnegative category).
-/
def conditionalNormalizationPathObstruction_claim55455 : Prop :=
  ∀ {V : Type*} [DecidableEq V] (ℓ : ℕ),
    0 < ℓ →
    ∀ (P : Fin (ℓ + 1) → V), Function.Injective P →
    ∀ (s : ℕ), 0 < s →
    ∀ (Q : Fin s → Fin ℓ → ℝ),
      (∀ (j : Fin s) (i : Fin ℓ), 0 ≤ Q j i) →
      (∀ (i : Fin ℓ), ∑ j : Fin s, Q j i = 1) →
      ∀ (j₀ : Fin s),
        (∃ i : Fin ℓ, Q j₀ i ≠ 0) →
        (∃ i : Fin ℓ, Q j₀ i = 0) →
        (∀ (r : Fin ℓ → ℝ),
          (∀ i, 0 ≤ r i) →
          realPathIncidence P (fun i => Q j₀ i + r i) =
            realPathEndpointBoundary P →
          (∀ i, r i = 1 - Q j₀ i) ∧
            (∀ i, Q j₀ i + r i = 1) ∧
            (∀ i, 0 < Q j₀ i + r i) ∧
            (∀ i, r i =
              ∑ j : Fin s, if j ≠ j₀ then Q j i else 0)) ∧
        ¬ ∃ r : Fin ℓ → ℝ,
          samePathLocalizedNonnegativeRepair P (Q j₀) r

end MathlibPlus.Open.ResearchFormalize
