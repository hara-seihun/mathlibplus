import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R3728InfiniteTranslations

noncomputable section

/-- Claim 50191: the odd integer numerator C controls all integral
translations, and the order of 2 modulo C supplies an infinite positive
complementary-start sequence. -/
def infiniteComplementaryTranslations_claim50191 : Prop :=
  ∀ (D : Finset ℕ) (hD : D.Nonempty),
    (∀ d ∈ D, 1 ≤ d) →
      ∀ N : ℤ,
        let A : Finset ℕ → ℚ := fun E =>
          ∑ d ∈ E, ((2 : ℚ) ^ d)⁻¹
        let B : Finset ℕ → ℚ := fun E =>
          ∑ d ∈ E, (d : ℚ) * ((2 : ℚ) ^ d)⁻¹
        let complementary : Finset ℕ → ℤ → Prop := fun E K =>
          (K : ℚ) * A E + B E = 2
        complementary D N →
          let m : ℕ := D.max' hD
          let C : ℕ := ∑ d ∈ D, 2 ^ (m - d)
          C % 2 = 1 ∧ 0 < C ∧
            (∀ c : ℕ,
              let E : Finset ℕ := D.image (fun d => d + c)
              A E = ((2 : ℚ) ^ c)⁻¹ * A D ∧
                B E = ((2 : ℚ) ^ c)⁻¹ * (B D + c * A D) ∧
                let N_c : ℚ :=
                  (N : ℚ) - c +
                    ((2 : ℚ) ^ (m + 1)) *
                      ((2 : ℚ) ^ c - 1) / C
                (C = 1 →
                  ∃ z : ℤ, (z : ℚ) = N_c) ∧
                (C > 1 →
                  ∀ o : ℕ,
                    0 < o →
                    (∀ r : ℕ, C ∣ 2 ^ r - 1 ↔ o ∣ r) →
                      (o ∣ c → C ∣ 2 ^ c - 1))) ∧
            (C = 1 →
              ∃ f : ℕ → ℤ,
                (∀ c : ℕ, 1 ≤ c →
                  let E : Finset ℕ := D.image (fun d => d + c)
                  let N_c : ℚ :=
                    (N : ℚ) - c +
                      ((2 : ℚ) ^ (m + 1)) *
                        ((2 : ℚ) ^ c - 1) / C
                  (f c : ℚ) = N_c ∧ complementary E (f c)) ∧
                ∃ c₀ : ℕ, 1 ≤ c₀ ∧
                  ∀ c : ℕ, c₀ ≤ c → 0 < f c ∧ f c < f (c + 1)) ∧
            (C > 1 →
              ∃ o : ℕ,
                0 < o ∧
                (∀ r : ℕ, C ∣ 2 ^ r - 1 ↔ o ∣ r) ∧
                ∃ f : ℕ → ℤ,
                  (∀ t : ℕ, 1 ≤ t →
                    let c : ℕ := o * t
                    let E : Finset ℕ := D.image (fun d => d + c)
                    let N_c : ℚ :=
                      (N : ℚ) - c +
                        ((2 : ℚ) ^ (m + 1)) *
                          ((2 : ℚ) ^ c - 1) / C
                    (f t : ℚ) = N_c ∧ complementary E (f t)) ∧
                  ∃ t₀ : ℕ, 1 ≤ t₀ ∧
                    ∀ t : ℕ, t₀ ≤ t → 0 < f t ∧ f t < f (t + 1))

end

end MathlibPlus.Open.ResearchFormalization.R3728InfiniteTranslations
