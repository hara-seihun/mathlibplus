import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalizationBatch.Charlier

/-- The fixed central Charlier parameter. -/
def claim4799_a : ℝ := 5 / 4

/-- The polynomial sequence given by the central Charlier recurrence. -/
def claim4799_polynomial : ℕ → Polynomial ℝ
  | 0 => 1
  | k + 1 =>
      Polynomial.X * Polynomial.derivative (claim4799_polynomial k) +
        (Polynomial.C claim4799_a - Polynomial.X) * claim4799_polynomial k

/-- Evaluation notation for the sequence in the admitted claims. -/
def claim4799_P (k : ℕ) (q : ℝ) : ℝ :=
  Polynomial.eval q (claim4799_polynomial k)

/-- The recurrence, written as a proposition over the explicitly defined sequence. -/
def claim4799_centralCharlierRecurrence : Prop :=
  claim4799_polynomial 0 = 1 ∧
    ∀ k : ℕ,
      claim4799_polynomial (k + 1) =
        Polynomial.X * Polynomial.derivative (claim4799_polynomial k) +
          (Polynomial.C claim4799_a - Polynomial.X) * claim4799_polynomial k

/-- The Euler operator `θ = q d/dq` on real-valued functions. -/
def claim4800_theta (f : ℝ → ℝ) : ℝ → ℝ :=
  fun q => q * deriv f q

/-- The shifted Euler operator `a + θ`. -/
def claim4800_shiftedEuler (f : ℝ → ℝ) : ℝ → ℝ :=
  fun q => claim4799_a * f q + claim4800_theta f q

/-- Iteration of the shifted Euler operator. -/
def claim4800_shiftedEulerIterate : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, f => f
  | k + 1, f => claim4800_shiftedEuler (claim4800_shiftedEulerIterate k f)

/-- Euler-operator representation of the central Charlier polynomials. -/
def claim4800_eulerOperatorRepresentation : Prop :=
  ∀ (k : ℕ) (q : ℝ),
    claim4799_P k q =
      Real.exp q * claim4800_shiftedEulerIterate k (fun z => Real.exp (-z)) q

/-- Exponential generating function of the central Charlier sequence. -/
def claim4801_exponentialGeneratingFunction : Prop :=
  ∀ (q t : ℝ),
    ∑' k : ℕ, claim4799_P k q * t ^ k / (Nat.factorial k : ℝ) =
      Real.exp (claim4799_a * t + q * (1 - Real.exp t))

/-- The analytically continued negative-intensity Poisson/umbral formula. -/
def claim4802_negativeIntensityPoissonFormula : Prop :=
  ∀ (k : ℕ) (q : ℝ),
    claim4799_P k q =
      Real.exp q *
        ∑' n : ℕ,
          (-q) ^ n / (Nat.factorial n : ℝ) * (claim4799_a + n) ^ k

/-- A real zero of a member of the sequence. -/
def claim4807_isRoot (k : ℕ) (q : ℝ) : Prop :=
  claim4799_P k q = 0

/-- Every positive-rank polynomial has exactly its simple positive real zeros. -/
def claim4807_simplePositiveRoots : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    Set.ncard {q : ℝ | claim4807_isRoot k q} = k ∧
      ∀ q : ℝ, claim4807_isRoot k q →
        0 < q ∧
          Polynomial.eval q (Polynomial.derivative (claim4799_polynomial k)) ≠ 0

/-- Strict consecutive interlacing, expressed by the ordered-root intervals. -/
def claim4808_strictConsecutiveInterlacing : Prop :=
  ∀ k : ℕ, ∀ hk : 1 ≤ k,
    ∀ ρ : Fin k → ℝ,
      StrictMono ρ →
      (∀ i : Fin k, 0 < ρ i) →
      (∀ i : Fin k, claim4807_isRoot k (ρ i)) →
      (∀ q : ℝ, claim4807_isRoot k q → q ∈ Set.range ρ) →
      let first : Fin k := ⟨0, Nat.pos_of_ne_zero (by omega)⟩
      let last : Fin k := ⟨k - 1, by omega⟩
      Set.ncard {q : ℝ | claim4807_isRoot (k + 1) q} = k + 1 ∧
        (∃ z : ℝ,
          claim4807_isRoot (k + 1) z ∧ 0 < z ∧ z < ρ first) ∧
        (∀ i : Fin (k - 1),
          ∃ z : ℝ,
            claim4807_isRoot (k + 1) z ∧
              ρ (Fin.castLT i.castSucc (by omega)) < z ∧
              z < ρ (Fin.castLT i.succ (by omega))) ∧
        (∃ z : ℝ,
          claim4807_isRoot (k + 1) z ∧ ρ last < z)

/-- Iterated polynomial differentiation. -/
def claim4810_iteratedPolynomialDerivative : ℕ → Polynomial ℝ → Polynomial ℝ
  | 0, p => p
  | n + 1, p =>
      Polynomial.derivative (claim4810_iteratedPolynomialDerivative n p)

/-- The even central-Charlier Wronskian polynomial. -/
def claim4810_wronskianPolynomial (r : ℕ) : Polynomial ℝ :=
  Matrix.det (fun i j : Fin r =>
    claim4810_iteratedPolynomialDerivative i.1
      (claim4799_polynomial (2 * j.1)))

/-- The Wronskian evaluated at `q`, with derivative rows made explicit. -/
def claim4810_evenCentralCharlierWronskian (r : ℕ) (q : ℝ) : ℝ :=
  Matrix.det (fun i j : Fin r =>
    Polynomial.eval q
      (claim4810_iteratedPolynomialDerivative i.1
        (claim4799_polynomial (2 * j.1))))

/-- The even central-Charlier Wronskian has the admitted degree. -/
def claim4811_wronskianDegree : Prop :=
  ∀ r : ℕ,
    Polynomial.natDegree (claim4810_wronskianPolynomial r) =
      r * (r - 1) / 2

end MathlibPlus.Open.ResearchFormalizationBatch.Charlier
