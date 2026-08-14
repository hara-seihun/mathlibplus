import Mathlib

noncomputable section

namespace MathlibPlus.Open.Research

def realEntire2277 (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧
    ∀ z : ℂ,
      f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z)

def rectangle2277 (a b c : ℝ) : Set ℂ :=
  {z | a ≤ z.re ∧ z.re ≤ b ∧ -c ≤ z.im ∧ z.im ≤ c}

/-- Admitted Claim 2277, with the finite simple-zero disk conclusion made explicit. -/
def claim2277 : Prop :=
  ∀ (a b c : ℝ) (fseq : ℕ → ℂ → ℂ) (f : ℂ → ℂ),
    a ≤ b →
      0 ≤ c →
        (∀ n : ℕ, realEntire2277 (fseq n)) →
          realEntire2277 f →
            let R : Set ℂ := rectangle2277 a b c
            (∀ z : ℂ, z ∈ frontier R → f z ≠ 0) →
              (∀ z : ℂ, z ∈ R → f z = 0 → z.im = 0 ∧ deriv f z ≠ 0) →
                (∃ U : Set ℂ,
                  IsOpen U ∧
                    (∀ z : ℂ, z ∈ R → z ∈ U) ∧
                      (∀ ε : ℝ, 0 < ε →
                        ∃ N : ℕ,
                          ∀ n : ℕ, N ≤ n →
                            ∀ z : ℂ, z ∈ U →
                              ‖fseq n z - f z‖ < ε)) →
                  ∃ N : ℕ,
                    (∀ n : ℕ, N ≤ n →
                      ∀ z : ℂ, z ∈ R →
                        fseq n z = 0 →
                          z.im = 0 ∧ deriv (fseq n) z ≠ 0) ∧
                      (∃ (k : ℕ) (centers : Fin k → ℂ) (radii : Fin k → ℝ),
                        (∀ i : Fin k,
                          f (centers i) = 0 ∧
                            centers i ∈ R ∧
                              (centers i).im = 0 ∧
                                deriv f (centers i) ≠ 0 ∧ 0 < radii i) ∧
                          (∀ i j : Fin k, i ≠ j →
                            radii i + radii j <
                              dist (centers i) (centers j)) ∧
                          (∀ i : Fin k, ∀ z : ℂ,
                            dist ((starRingEnd ℂ) z) (centers i) < radii i ↔
                              dist z (centers i) < radii i) ∧
                          (∀ z : ℂ, z ∈ R → f z = 0 →
                            ∃ i : Fin k, z = centers i) ∧
                          (∀ n : ℕ, N ≤ n →
                            ∀ i : Fin k,
                              (∃! z : ℂ,
                                dist z (centers i) < radii i ∧ fseq n z = 0) ∧
                                (∀ z : ℂ,
                                  dist z (centers i) < radii i →
                                    fseq n z = 0 → deriv (fseq n) z ≠ 0)) ∧
                          (∀ n : ℕ, N ≤ n →
                            ∀ z : ℂ, z ∈ R → fseq n z = 0 →
                              ∃ i : Fin k,
                                dist z (centers i) < radii i))

end MathlibPlus.Open.Research
