import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

open scoped BigOperators

/-- Claim 3347: no `(5,5)`-good graph of order 43 is 24-regular,
with the stated complementary formulation. -/
def claim3347 : Prop :=
  (∀ {V : Type*} [Fintype V], Fintype.card V = 43 →
    ¬ ∃ G : SimpleGraph V,
      (G.CliqueFree 5 ∧ G.IndepSetFree 5) ∧
        (∀ v, (G.neighborSet v).ncard = 24)) ∧
  (∀ {V : Type*} [Fintype V], Fintype.card V = 43 →
    ∀ G : SimpleGraph V,
      (G.CliqueFree 5 ∧ G.IndepSetFree 5) →
      (∀ v, (G.neighborSet v).ncard = 24) →
      (Gᶜ).CliqueFree 5 ∧ (Gᶜ).IndepSetFree 5 ∧
        (∀ v, ((Gᶜ).neighborSet v).ncard = 18))

/-- Claim 59757: the limiting telescoping identity and its absolute-value bound. -/
def claim59757 : Prop :=
  ∀ (p : ℕ → ℝ) (q : ℝ) (M : ℕ),
    q ≠ 0 →
    Filter.Tendsto p Filter.atTop (nhds q) →
    Summable (fun k : ℕ =>
      |(p (M + k + 1) - p (M + k)) / q|) →
    (q - p M) / q =
        ∑' k : ℕ, (p (M + k + 1) - p (M + k)) / q ∧
      |(q - p M) / q| ≤
        ∑' k : ℕ, |(p (M + k + 1) - p (M + k)) / q|

end MathlibPlus.Open.ResearchFormalization
