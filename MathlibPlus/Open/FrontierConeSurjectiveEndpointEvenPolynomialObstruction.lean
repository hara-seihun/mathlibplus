import Mathlib

namespace MathlibPlus.Open

/--
There are real-valued functions with a surjective endpoint coordinate and
strictly positive increasing bounds, together with an even,
conjugation-equivariant complex polynomial having a nonreal zero.
-/
def frontier_cone_surjective_endpoint_even_polynomial_obstruction : Prop :=
  ∃ (P : ℝ → ℝ) (H : ℕ → ℝ → ℝ) (F : ℂ → ℂ),
    P 0 ≠ 0 ∧
    Function.Surjective (fun y : ℝ => P (-y) / P 0) ∧
    (∀ (N : ℕ) (q : ℝ),
      H N q ≥ (N + 1 : ℝ) ∧ (N + 1 : ℝ) > 0) ∧
    (∀ (N : ℕ) (q : ℝ), H N q < H (N + 1) q) ∧
    (∀ (N : ℕ) (y : ℝ), H N (P (-y) / P 0) > 0) ∧
    (∃ p : Polynomial ℂ,
      (∀ z : ℂ, F z = p.eval z) ∧
      (∀ z : ℂ, F (-z) = F z) ∧
      (∀ z : ℂ, F (star z) = star (F z))) ∧
    (∃ z : ℂ, F z = 0 ∧ z.im ≠ 0) ∧
    (∀ x : ℝ, P x = x + 1) ∧
    (∀ (N : ℕ) (q : ℝ), H N q = q ^ 2 + N + 1) ∧
    (∀ z : ℂ, F z = z ^ 2 + 1) ∧
    F Complex.I = 0 ∧
    Complex.I.im = 1

end MathlibPlus.Open
