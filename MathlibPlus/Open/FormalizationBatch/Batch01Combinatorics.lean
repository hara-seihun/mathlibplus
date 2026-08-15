import Mathlib

namespace MathlibPlus.Open.FormalizationBatch.Combinatorics

open scoped BigOperators
noncomputable section
open Classical
local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance decEq (α : Type*) : DecidableEq α := Classical.decEq α

private def factorialProfile (V : ℕ → ℕ) : Prop :=
  V 1 = 1 ∧ V 2 = 1 ∧
    ∀ n : ℕ, 3 ≤ n →
      V n = 1 +
        ∑ t ∈ Finset.Icc 2 (n - 1),
          (Nat.choose n t / (n / t)) * V (n - t + 1)

/-- Claim 31266: the independent scalar closure has factorial growth. -/
def claim31266_factorialMatchingTraceObstruction : Prop :=
  ∃ V : ℕ → ℕ,
    factorialProfile V ∧
    (∀ n : ℕ, 2 ≤ n →
      Nat.choose n 2 / (n / 2) = if Even n then n - 1 else n) ∧
    (∀ n : ℕ, 2 ≤ n → Nat.factorial (n - 1) ≤ V n)

private def supportOf {α : Type*} {m : ℕ} (F : Fin m → Finset α) (x : α) : Finset (Fin m) :=
  Finset.univ.filter (fun i => x ∈ F i)

private def supportLaminar {α : Type*} {m : ℕ} (F : Fin m → Finset α) : Prop :=
  ∀ x y : α, (supportOf F x).Nonempty → (supportOf F y).Nonempty →
    supportOf F x ⊆ supportOf F y ∨
    supportOf F y ⊆ supportOf F x ∨
    Disjoint (supportOf F x) (supportOf F y)

private def selectedSunflower {α : Type*} {m k : ℕ} (F : Fin m → Finset α)
    (sel : Fin k → Fin m) : Prop :=
  ∃ core : Finset α, ∀ i j : Fin k, i ≠ j →
    F (sel i) ∩ F (sel j) = core

private def selectedSupportCondition {α : Type*} {m k : ℕ} (F : Fin m → Finset α)
    (sel : Fin k → Fin m) : Prop :=
  ∀ x : α,
    ((supportOf F x).filter (fun i => i ∈ Finset.univ.filter (fun j => j ∈ Set.range sel))).card =
      0 ∨
    ((supportOf F x).filter (fun i => i ∈ Finset.univ.filter (fun j => j ∈ Set.range sel))).card =
      1 ∨
    ((supportOf F x).filter (fun i => i ∈ Finset.univ.filter (fun j => j ∈ Set.range sel))).card = k

/-- Claim 31276: laminar supports characterize selected sunflowers. -/
def claim31276_laminarIncidenceSupports : Prop :=
  ∀ {α : Type*} [Fintype α] (m r k : ℕ) (F : Fin m → Finset α),
    (∀ i : Fin m, (F i).card = r) → Function.Injective F →
    supportLaminar F →
    ∀ sel : Fin k → Fin m, Function.Injective sel →
      (selectedSunflower F sel ↔ selectedSupportCondition F sel)

end
end MathlibPlus.Open.FormalizationBatch.Combinatorics
