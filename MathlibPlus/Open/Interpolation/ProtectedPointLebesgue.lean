import Mathlib

namespace MathlibPlus.Open.Interpolation

private noncomputable def prefixLebesgueFunction (x : ℕ → ℝ) (n : ℕ) (a : ℝ) : ℝ :=
  Finset.sum (Finset.univ : Finset (Fin n)) (fun i : Fin n =>
    |Finset.prod ((Finset.univ : Finset (Fin n)).erase i) (fun j : Fin n =>
      (a - x j.1) / (x i.1 - x j.1))|)

/-- Every finite set of points in `(-1, 1)` admits one infinite sequence of
pairwise distinct nodes in that interval whose every prefix has uniformly
bounded Lebesgue function on the protected set. -/
def finiteProtectedPointNestedLebesgue : Prop :=
  ∀ F : Set ℝ, F.Finite → F ⊆ Set.Ioo (-1 : ℝ) 1 →
    ∃ x : ℕ → ℝ,
      Function.Injective x ∧
      (∀ n : ℕ, x n ∈ Set.Ioo (-1 : ℝ) 1) ∧
      ∃ C_F : ℝ,
        ∀ n : ℕ, 0 < n → ∀ a : ℝ, a ∈ F →
          prefixLebesgueFunction x n a ≤ C_F

end MathlibPlus.Open.Interpolation
