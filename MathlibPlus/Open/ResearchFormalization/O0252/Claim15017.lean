import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch_01a0067d
import MathlibPlus.Open.ResearchFormalization.O0252.Claim15011

open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory Set

namespace MathlibPlus.Open.ResearchFormalization.O0252

noncomputable section

private def transitionScale15017 (k L : ℕ) : ℝ :=
  Real.rpow (L : ℝ) ((1 : ℝ) / (2 * (k : ℝ)))

private def kappa15017 (α y : ℝ) (k : ℕ) : ℝ :=
  Real.rpow (((5 / 2 : ℝ) - y) / α)
    ((1 : ℝ) / (2 * (k : ℝ)))

private def xOne15017 (k : ℕ) (α y₁ : ℝ) (L : ℕ) : ℝ :=
  kappa15017 α y₁ k * transitionScale15017 k L

private def xTwo15017 (k : ℕ) (α y₀ : ℝ) (L : ℕ) : ℝ :=
  kappa15017 α y₀ k * transitionScale15017 k L

private def horizontalProfilePolynomial15017
    (P : ℕ → Polynomial ℝ) (k L : ℕ) (y : ℝ) : Polynomial ℂ :=
  (P L).map Complex.ofRealHom |>.comp
    (Polynomial.C (((transitionScale15017 k L : ℂ) ^ 2)⁻¹) *
      (Polynomial.X + Polynomial.C (Complex.I * (y : ℂ))) ^ 2)

private def realLength15017 (E : Set ℝ) : ℝ :=
  ENNReal.toReal (volume E)

private def supNorm15017 (Q : Polynomial ℂ) (E : Set ℝ) : ℝ :=
  sSup {r : ℝ | ∃ x : ℝ, x ∈ E ∧
    r = ‖Polynomial.eval (x : ℂ) Q‖}

private def complexRemezBound15017
    (n : ℕ) (J E : Set ℝ) (Q : Polynomial ℂ) : Prop :=
  (0 < realLength15017 E ∧ E ⊆ J ∧ Q.natDegree ≤ n) →
    supNorm15017 Q J ≤
      (4 * realLength15017 J / realLength15017 E) ^ n *
        supNorm15017 Q E

private def intervalLike15017 (E : Set ℝ) : Prop :=
  ∀ x ∈ E, ∀ z ∈ E, ∀ y : ℝ, x ≤ y → y ≤ z → y ∈ E

private def atMostIntervalComponents15017
    (E : Set ℝ) (N : ℕ) : Prop :=
  ∃ m : ℕ, m ≤ N ∧
    ∃ C : Fin m → Set ℝ,
      E = ⋃ i : Fin m, C i ∧
        (∀ i, (C i).Nonempty ∧ intervalLike15017 (C i)) ∧
        (∀ i j, i ≠ j → Disjoint (C i) (C j))

private def profileSublevel15017
    (k : ℕ) (α : ℝ) (P : ℕ → Polynomial ℝ)
    (y₀ y₁ δ y : ℝ) (L : ℕ) : Set ℝ :=
  {x : ℝ |
    x ∈ Set.Icc (xOne15017 k α y₁ L) (xTwo15017 k α y₀ L) ∧
      ‖Polynomial.eval (x : ℂ)
          (horizontalProfilePolynomial15017 P k L y)‖ ≤
        Real.exp (-δ * (L : ℝ) / 4)}

/-- Claim 15017: the degree-sensitive complex Remez bound, applied on the
actual kappa-defined transition interval, gives the stated profile sublevel
length, the zero-degree case, and the finite interval-union control. -/
def claim15017_complexRemezProfileSublevel : Prop :=
  ∀ (k : ℕ) (α : ℝ) (P : ℕ → Polynomial ℝ)
    (coeff : ℕ → ℕ → ℝ) (d : ℕ → ℕ) (B : ℕ → ℝ)
    (y₀ y₁ δ y : ℝ),
    admissiblePolynomialProfileClass P coeff d B k →
    0 < α →
    0 < y₀ →
    y₀ < y₁ →
    y₁ < 1 / 2 →
    0 < δ →
    δ < (1 / 2 : ℝ) * min y₀ ((1 / 2 : ℝ) - y₁) →
    0 < y →
    ∃ C c : ℝ,
      0 < C ∧
        0 < c ∧
          IsLittleO atTop
            (fun L : ℕ =>
              realLength15017
                (profileSublevel15017 k α P y₀ y₁ δ y L))
            (fun L : ℕ => transitionScale15017 k L) ∧
            ∀ᶠ L : ℕ in atTop,
              let Q := horizontalProfilePolynomial15017 P k L y
              let J := Set.Icc
                (xOne15017 k α y₁ L)
                (xTwo15017 k α y₀ L)
              let E := profileSublevel15017 k α P y₀ y₁ δ y L
              complexRemezBound15017 (2 * d L) J E Q ∧
                Q.natDegree ≤ 2 * d L ∧
                (d L = 0 → realLength15017 E = 0) ∧
                (0 < d L →
                  realLength15017 E ≤
                    C * transitionScale15017 k L *
                      Real.exp (-c * (L : ℝ) / (d L : ℝ))) ∧
                atMostIntervalComponents15017 E
                  (Nat.ceil (C * ((d L : ℝ) + 1)))

end

end MathlibPlus.Open.ResearchFormalization.O0252
