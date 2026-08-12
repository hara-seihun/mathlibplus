import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace MathlibPlus.Algebra

/-- The generic one-block algebra behind claim 26295.  The symmetric side-forest
matrix has entries `[[α, β], [β, 0]]`; the displayed invariant is retained as
an exact polynomial relation rather than as an informal matching-state label. -/
theorem pathPalindromeBlock_claim26295
    {R : Type*} [CommRing R]
    (x y z u p m n α β : R)
    (h : x * (m - n) = p * (z - y)) :
    let c₀ : R := α * x * p + β * x * m + β * y * p
    let c₁ : R := α * z * p + β * z * m + β * u * p
    let d₀ : R := α * x * p + β * x * n + β * z * p
    let d₁ : R := α * y * p + β * y * n + β * u * p
    (c₀ = d₀) ∧
      (x * c₀ = d₀ * x) ∧
      (y * c₀ + x * c₁ = d₁ * x + d₀ * z) ∧
      (x * (c₁ - d₁) = c₀ * (z - y)) := by
  dsimp
  have hc :
      α * x * p + β * x * m + β * y * p =
        α * x * p + β * x * n + β * z * p := by
    linear_combination β * h
  refine ⟨hc, ?_, ?_, ?_⟩
  · rw [hc]
    ring
  · linear_combination β * (y + z) * h
  · linear_combination β * y * h

/-- The root-potential relation in claim 26295 is closed under any finite list
of symmetric blocks.  The one-step product-state equalities are supplied by
`pathPalindromeBlock_claim26295`; this theorem records the iterated invariant. -/
theorem pathPalindromeBlock_composition_claim26295
    {R : Type*} [CommRing R]
    (x y z u : R) :
    ∀ (blocks : List (R × R)) (p m n : R),
      x * (m - n) = p * (z - y) →
      let step : (R × R × R) → (R × R) → (R × R × R) :=
        fun state block =>
          let α := block.1
          let β := block.2
          let p₀ := state.1
          let m₀ := state.2.1
          let n₀ := state.2.2
          (α * x * p₀ + β * x * m₀ + β * y * p₀,
            α * z * p₀ + β * z * m₀ + β * u * p₀,
            α * y * p₀ + β * y * n₀ + β * u * p₀)
      let out := List.foldl step (p, m, n) blocks
      x * (out.2.1 - out.2.2) = out.1 * (z - y) := by
  intro blocks
  induction blocks with
  | nil =>
      intro p m n h
      simp
      exact h
  | cons block blocks ih =>
      intro p m n h
      let α := block.1
      let β := block.2
      let p₀ := α * x * p + β * x * m + β * y * p
      let m₀ := α * z * p + β * z * m + β * u * p
      let n₀ := α * y * p + β * y * n + β * u * p
      have hnext : x * (m₀ - n₀) = p₀ * (z - y) := by
        dsimp [p₀, m₀, n₀]
        linear_combination β * y * h
      have htail := ih p₀ m₀ n₀ hnext
      simpa [List.foldl, α, β, p₀, m₀, n₀] using htail

end MathlibPlus.Algebra
