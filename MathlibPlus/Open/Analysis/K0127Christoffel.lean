import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Christoffel expectation identity for the explicitly normalized
squared-Vandermonde ensemble and its fixed negative-axis tilt. -/
def claim8925 : Prop :=
  ∀ (z ω : ℕ → ℕ → ℝ) (n : ℕ) (s s₀ : ℝ) (p : Polynomial ℝ),
    0 < n →
    0 < s →
    0 < s₀ →
    (∀ i, 0 < z n i) →
    (∀ i j, i < j → z n j < z n i) →
    (∀ i, 0 < ω n i) →
    let W : ({S : Finset ℕ // S.card = n} → ℝ) := fun S =>
      (∏ i : S.1, ω n i.1) *
        (∏ i : S.1,
          ∏ j : S.1,
            if i.1 < j.1 then
              ((z n i.1) ^ 2 - (z n j.1) ^ 2) ^ 2
            else 1)
    let Z : ℝ := ∑' S : {S : Finset ℕ // S.card = n}, W S
    let P : ({S : Finset ℕ // S.card = n} → ℝ) := fun S => W S / Z
    let H : ℝ → ({S : Finset ℕ // S.card = n} → ℝ) := fun r S =>
      ∏ i : S.1, (r + (z n i.1) ^ 2)
    let Ztilt : ℝ :=
      ∑' S : {S : Finset ℕ // S.card = n}, P S * H s₀ S
    let Ptilt : ({S : Finset ℕ // S.card = n} → ℝ) := fun S =>
      P S * H s₀ S / Ztilt
    Summable W →
    0 < Z →
    Summable (fun S : {S : Finset ℕ // S.card = n} => P S * H s₀ S) →
    0 < Ztilt →
    p.Monic →
    p.natDegree = n →
    (∀ q : Polynomial ℝ, q.natDegree < n →
      Summable (fun i : ℕ =>
        ω n i * p.eval ((z n i) ^ 2) * q.eval ((z n i) ^ 2)) ∧
      (∑' i : ℕ,
        ω n i * p.eval ((z n i) ^ 2) * q.eval ((z n i) ^ 2)) = 0) →
    p.eval (-s) / p.eval (-s₀) =
      ∑' S : {S : Finset ℕ // S.card = n},
        Ptilt S *
          Real.exp ((n : ℝ) *
            ((n : ℝ)⁻¹ *
              (∑ i : S.1,
                Real.log ((s + (z n i.1) ^ 2) /
                  (s₀ + (z n i.1) ^ 2)))))

end MathlibPlus.Open.Analysis
