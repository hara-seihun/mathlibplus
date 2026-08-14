import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

private def unionClosed {α : Type} [DecidableEq α]
    (𝒜 : Finset (Finset α)) : Prop :=
  ∀ ⦃A B : Finset α⦄, A ∈ 𝒜 → B ∈ 𝒜 → A ∪ B ∈ 𝒜

private def emptyTotalIntersection {α : Type} [DecidableEq α]
    (𝒜 : Finset (Finset α)) : Prop :=
  ∀ x : α, ∃ A : Finset α, A ∈ 𝒜 ∧ x ∉ A

private def unionProduct {α : Type} [DecidableEq α]
    (𝒜 ℬ : Finset (Finset α)) : Finset (Finset α) :=
  𝒜.biUnion (fun A => ℬ.image (fun B => A ∪ B))

/-- The pair-fiber union-product floor and its sharp three-element example. -/
def pairFiberUnionProductFloor : Prop :=
  (∀ {α : Type} [DecidableEq α] (𝒜 ℬ : Finset (Finset α)),
    𝒜.Nonempty →
    ℬ.Nonempty →
    ∅ ∉ 𝒜 →
    ∅ ∉ ℬ →
    unionClosed 𝒜 →
    unionClosed ℬ →
    emptyTotalIntersection 𝒜 →
    emptyTotalIntersection ℬ →
    3 ≤ (unionProduct 𝒜 ℬ).card) ∧
  (let sharpExample : Finset (Finset ℕ) :=
      {({1} : Finset ℕ), {2}, {1, 2}}
   unionClosed sharpExample ∧
   emptyTotalIntersection sharpExample ∧
   ∅ ∉ sharpExample ∧
   sharpExample.Nonempty ∧
   (unionProduct sharpExample sharpExample).card = 3)

private noncomputable def polynomialHouse (p : Polynomial ℤ) : ℝ :=
  sSup {r : ℝ | ∃ z : ℂ, (p.map (algebraMap ℤ ℂ)).eval z = 0 ∧ r = ‖z‖}

private noncomputable def lehmerPolynomial : Polynomial ℤ :=
  Polynomial.X ^ 10 + Polynomial.X ^ 9 - Polynomial.X ^ 7 - Polynomial.X ^ 6 -
      Polynomial.X ^ 5 - Polynomial.X ^ 4 - Polynomial.X ^ 3 + Polynomial.X + 1

private noncomputable def lehmerPaddedPolynomial : Polynomial ℤ :=
  lehmerPolynomial * (Polynomial.X + 1) ^ 22

private noncomputable def polynomialMahlerMeasure (p : Polynomial ℤ) : ℝ := by
  classical
  exact ((p.map (algebraMap ℤ ℂ)).roots.map (fun z => max 1 ‖z‖)).prod

private noncomputable def lehmerNumber : ℝ :=
  sSup {x : ℝ |
    1 < x ∧ (lehmerPolynomial.map (algebraMap ℤ ℝ)).eval x = 0}

/-- Lehmer's polynomial padded by a cyclotomic factor preserves Mahler measure. -/
def lehmerPaddedReciprocalPolynomial : Prop :=
  lehmerPaddedPolynomial.Monic ∧
  lehmerPaddedPolynomial.natDegree = 32 ∧
  lehmerPaddedPolynomial.reverse = lehmerPaddedPolynomial ∧
  Polynomial.X + 1 = Polynomial.cyclotomic 2 ℤ ∧
  polynomialMahlerMeasure lehmerPaddedPolynomial =
    polynomialMahlerMeasure lehmerPolynomial ∧
  polynomialMahlerMeasure lehmerPolynomial = lehmerNumber

/-- Power-of-two skew-reciprocal factor dichotomy. -/ 
def powerOfTwoSkewReciprocalFactorDichotomy : Prop :=
  ∀ (i : ℕ) (p : Polynomial ℤ),
    p.Monic →
    p.natDegree = 2 ^ (i + 1) →
    p.reverse = -p →
    1 < polynomialHouse p →
    ((∃ G : Polynomial ℤ,
        G.reverse = G ∧
        p = G.comp (Polynomial.X ^ 2)) ∨
      (∃ q : Polynomial ℤ,
        q.Monic ∧
        q ∣ p ∧
        Irreducible q ∧
        q.reverse ≠ q ∧
        q ≠ Polynomial.X - Polynomial.C 1))

/-- A continuous nonvanishing branch on a rectangle admits a continuous phase lift. -/
def continuousPhaseLiftForNonvanishingSelectedBranch : Prop :=
  ∀ (τ T X Y : ℝ),
    let D : Set (ℝ × ℝ) := Set.Icc τ T ×ˢ Set.Icc X Y
    ∀ E : D → ℂ,
      Continuous E →
      (∀ p, E p ≠ 0) →
      ∃ θ : D → ℝ,
        Continuous θ ∧
        (∀ p, E p = (‖E p‖ : ℂ) * Complex.exp (Complex.I * (θ p : ℂ)))

/-- Zeros of twice the real part carry integer half-phase labels. -/
def integerHalfPhaseLabelsOnRealZeroSet : Prop :=
  ∀ (τ T X Y : ℝ),
    let D : Set (ℝ × ℝ) := Set.Icc τ T ×ˢ Set.Icc X Y
    ∀ E : D → ℂ,
      Continuous E →
      (∀ p, E p ≠ 0) →
      ∀ θ : D → ℝ,
        Continuous θ →
        (∀ p, E p = (‖E p‖ : ℂ) * Complex.exp (Complex.I * (θ p : ℂ))) →
        ∀ p, 2 * (E p).re = 0 →
          ∃ k : ℤ, θ p / Real.pi = (k : ℝ) + (1 / 2 : ℝ)

end MathlibPlus.Open.ResearchFormalization
