import Mathlib

namespace MathlibPlus.Analysis.Claim40836

/-!
The finite-domain counterexample from admitted claim 40836.  On `Bool`, the
separate maxima of `f` and `g` are both positive, but the pointwise product is
zero everywhere, so its maximum is zero as well.
-/
theorem product_of_separate_suprema_not_common_point_witness_claim40836 :
    ∃ f g : Bool → ℝ,
      (∀ x, 0 ≤ f x) ∧
      (∀ x, 0 ≤ g x) ∧
      f true = 1 ∧
      f false = 0 ∧
      g true = 0 ∧
      g false = 1 ∧
      max (f true) (f false) = 1 ∧
      max (g true) (g false) = 1 ∧
      (∀ x, f x * g x = 0) ∧
      max (f true * g true) (f false * g false) = 0 := by
  refine ⟨fun x => if x then 1 else 0, fun x => if x then 0 else 1, ?_⟩
  simp only [Bool.forall_bool]
  norm_num

end MathlibPlus.Analysis.Claim40836
