import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim21563

/--
The counting-inner-product form of the pullback Gram identity from claim 21563.
A map with every fibre of cardinality `2^d` pulls back counting inner products
by the scalar `2^d`.
-/
theorem pullbackGram_identity_claim21563
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (φ : α → β) (d : ℕ)
    (hfiber : ∀ b : β,
      (Finset.univ.filter (fun a : α => φ a = b)).card = 2 ^ d)
    (q r : β → ℝ) :
    ∑ a : α, q (φ a) * r (φ a) =
      (2 ^ d : ℝ) * ∑ b : β, q b * r b := by
  rw [← Finset.sum_fiberwise (s := (Finset.univ : Finset α))
    (g := φ) (f := fun a => q (φ a) * r (φ a))]
  simp_rw [show ∀ b : β,
      (∑ x ∈ Finset.univ.filter (fun a : α => φ a = b),
        q (φ x) * r (φ x)) =
      ((Finset.univ.filter (fun a : α => φ a = b)).card : ℝ) *
        (q b * r b) by
    intro b
    calc
      (∑ x ∈ Finset.univ.filter (fun a : α => φ a = b),
          q (φ x) * r (φ x)) =
          ∑ x ∈ Finset.univ.filter (fun a : α => φ a = b),
            q b * r b := by
              apply Finset.sum_congr rfl
              intro x hx
              have hxb : φ x = b := (Finset.mem_filter.mp hx).2
              rw [hxb]
      _ = (Finset.univ.filter (fun a : α => φ a = b)).card •
            (q b * r b) := by
              simpa using
                (Finset.sum_const
                  (s := Finset.univ.filter (fun a : α => φ a = b))
                  (b := q b * r b))
      _ = ((Finset.univ.filter (fun a : α => φ a = b)).card : ℝ) *
            (q b * r b) := by
              simp [nsmul_eq_mul]
    ]
  simp_rw [hfiber]
  rw [Finset.mul_sum]
  simp [Nat.cast_pow]

end MathlibPlus.LinearAlgebra.Claim21563
