import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-- The two-frequency family from admitted claim R-5433.2. -/
noncomputable def twoFrequency (a t : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (t : ℂ) * Complex.cos z +
    (a : ℂ) * Complex.exp ((4 * t : ℝ) : ℂ) * Complex.cos (2 * z)

noncomputable def oddPi (n : ℤ) : ℂ :=
  (((2 * (n : ℝ) + 1) * Real.pi : ℝ) : ℂ)

def allZerosReal (f : ℂ → ℂ) : Prop :=
  ∀ z, f z = 0 → z.im = 0

def doubleZero (f : ℂ → ℂ) (z : ℂ) : Prop :=
  f z = 0 ∧ deriv f z = 0 ∧ iteratedDeriv 2 f z ≠ 0

def allZerosSimple (f : ℂ → ℂ) : Prop :=
  ∀ z, f z = 0 → deriv f z ≠ 0

/-- Exact entire-function and zero-transition assertion of R-5433.2. -/
def claim54414 : Prop :=
  ∀ a : ℝ, 0 < a →
    (∀ t : ℝ, Differentiable ℂ (twoFrequency a t)) ∧
    (∀ t : ℝ, ∀ z : ℂ, twoFrequency a t (-z) = twoFrequency a t z) ∧
    (∀ t : ℝ,
      (allZerosReal (twoFrequency a t) ↔ t ≥ -(Real.log a) / 3) ∧
      (t = -(Real.log a) / 3 →
        ∀ n : ℤ, doubleZero (twoFrequency a t) (oddPi n)) ∧
      (t > -(Real.log a) / 3 →
        allZerosSimple (twoFrequency a t))) ∧
    (∀ t : ℝ, ∀ z : ℂ,
      let b : ℝ := a * Real.exp (3 * t)
      twoFrequency a t z = 0 ↔
        2 * (b : ℂ) * (Complex.cos z) ^ 2 + Complex.cos z - (b : ℂ) = 0) ∧
    (∀ b : ℝ, 0 < b →
      ((∀ y : ℝ, 2 * b * y ^ 2 + y - b = 0 → -1 ≤ y ∧ y ≤ 1) ↔
        b ≥ 1))

abbrev F3 := ZMod 3
abbrev V3 (n : ℕ) := Fin n → F3

def cubicShear (w : V3 3) : V3 5 :=
  ![w 0 * (w 1) ^ 2,
    w 0 * (w 2) ^ 2,
    (w 1) ^ 2 * w 2,
    w 1 * (w 2) ^ 2,
    w 0 * w 1 * w 2]

def fibreShear (w : V3 3) (h : V3 5) : V3 3 × V3 5 :=
  (w, h + cubicShear w)

def quotientShearExists (K : Submodule F3 (V3 5)) : Prop :=
  ∃ ψ : V3 3 × (V3 5 ⧸ K) → V3 3 × (V3 5 ⧸ K),
    ∀ w h,
      ψ (w, QuotientAddGroup.mk h) =
        (w, QuotientAddGroup.mk (h + cubicShear w))

/-- Exact cubic fibre translation and its descent assertion of R-4396.1. -/
def claim54432 : Prop :=
  ∀ K : Submodule F3 (V3 5), quotientShearExists K

noncomputable def componentCount {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  Nat.card (SimpleGraph.ConnectedComponent G)

noncomputable def deletionPolynomial {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Polynomial (Polynomial ℤ) :=
  ∑ S : Finset V,
    (Polynomial.X : Polynomial (Polynomial ℤ)) ^ S.card *
      Polynomial.C ((Polynomial.X : Polynomial ℤ) ^
        componentCount (G.induce {v | v ∉ (S : Set V)}))

noncomputable def deletionAtNegV {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Polynomial ℤ :=
  Polynomial.eval₂ (RingHom.id (Polynomial ℤ))
    (-(Polynomial.X : Polynomial ℤ)) (deletionPolynomial G)

noncomputable def responseStar {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Polynomial (Polynomial ℤ) := by
  classical
  exact ((Finset.univ : Finset (Finset V)).filter
      (fun K : Finset V => K.Nonempty ∧ (G.induce (K : Set V)).Connected)).sum
    (fun K : Finset V =>
      (Polynomial.X : Polynomial (Polynomial ℤ)) ^ (K.card - 1) *
        Polynomial.C (deletionAtNegV (G.induce (K : Set V))))

noncomputable def leafCount {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  Nat.card {v : V // Nat.card (G.neighborSet v) = 1}

def eisensteinResponseProperty {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  (responseStar G).Monic ∧
  (responseStar G).natDegree = Fintype.card V - 1 ∧
  (∀ k < Fintype.card V - 1,
    (Polynomial.X : Polynomial ℤ) ∣ (responseStar G).coeff k) ∧
  (Polynomial.X : Polynomial ℤ) ^ 2 ∣
    ((responseStar G).coeff 0 -
      Polynomial.C (leafCount G : ℤ) * (Polynomial.X : Polynomial ℤ)) ∧
  ¬ ((Polynomial.X : Polynomial ℤ) ^ 2 ∣ (responseStar G).coeff 0)

/-- Exact all-mark response and Eisenstein assertion of R-4390.1. -/
def claim54418 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V), T.IsTree → 3 ≤ Fintype.card V →
      eisensteinResponseProperty T

end MathlibPlus.Open.ResearchFormalizationBatch
