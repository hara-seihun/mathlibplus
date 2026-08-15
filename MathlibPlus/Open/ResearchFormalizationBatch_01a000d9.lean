import Mathlib

<<<<<<< ours
namespace MathlibPlus.Open.ResearchFormalizationBatch

open Filter Asymptotics MeasureTheory

/-- Claim 13632: exact first-column checkerboard formula and its stated
conditional little-o consequences. -/
def claim13632 : Prop :=
  ∀ (α b : ℝ) (t : ℕ → ℝ),
    let A : ℝ := b - α * t 0
    let K : ℕ → ℝ := fun n ↦
      (b * ((n + 1 : ℕ) : ℝ) - α * (n : ℝ) * t 0) * t n
        - α * ((n + 1 : ℕ) : ℝ) * (b - α * t 0) * t (n + 1)
    let m : ℕ → ℝ := fun n ↦ K n / K (n - 1)
    (IsLittleO atTop (fun n ↦ t (n + 1) / t n) (fun _ ↦ (1 : ℝ)) ∧
        0 < A) →
      IsLittleO atTop
          (fun n ↦ K n - A * (n : ℝ) * t n)
          (fun n ↦ A * (n : ℝ) * t n) ∧
        IsLittleO atTop
          (fun n ↦
            m n - ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) *
              (t n / t (n - 1)))
          (fun n ↦
            ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) *
              (t n / t (n - 1)))

/-- Claim 13633: first-shell dominance for the explicitly displayed theta
moments, with the displayed tail estimate interpreted at infinity. -/
def claim13633 : Prop :=
  ∀ (T : ℝ → ℝ),
    IsBigO atTop
        (fun u ↦ T u - Real.exp (-Real.pi * Real.exp (2 * u)))
        (fun u ↦
          Real.exp (-Real.pi * Real.exp (2 * u)) *
            Real.exp (-3 * Real.pi * Real.exp (2 * u))) →
      let I : ℕ → ℝ := fun n ↦
        ∫ u in Set.Ioi (0 : ℝ),
          Real.exp (u / 2) * T u * u ^ (2 * n)
      let t : ℕ → ℝ := fun n ↦
        2 * I n / (Nat.factorial (2 * n) : ℝ)
      let φ : ℕ → ℝ → ℝ := fun n u ↦
        (2 * n : ℝ) * Real.log u + u / 2 - Real.pi * Real.exp (2 * u)
      let J : ℕ → ℝ := fun n ↦
        ∫ u in Set.Ioi (0 : ℝ), Real.exp (φ n u)
      IsLittleO atTop (fun n ↦ I n - J n) (fun n ↦ J n)
=======
open scoped BigOperators Topology
open Filter

namespace MathlibPlus.Open.ResearchFormalizationBatch

noncomputable def c0184AdmissibleProfile
    (k : ℕ)
    (P : ℕ → Polynomial ℂ)
    (d : ℕ → ℕ)
    (B : ℕ → ℝ)
    (a : ℕ → ℕ → ℂ) : Prop :=
  1 ≤ k ∧
    (∀ L : ℕ,
      P L = 1 + Finset.sum (Finset.Icc 1 (d L)) (fun j => Polynomial.monomial j (a L j))) ∧
    (∀ (L j : ℕ), j ∈ Finset.Icc 1 (d L) → ‖a L j‖ ≤ (B L) ^ j) ∧
    Tendsto (fun L : ℕ => (B L) ^ k * (d L : ℝ) / (L : ℝ)) atTop (𝓝 0) ∧
    Tendsto
      (fun L : ℕ => (d L : ℝ) * Real.log (B L) / (L : ℝ))
      atTop (𝓝 0)

noncomputable def claim15009 : Prop :=
  ∀ (k : ℕ) (P : ℕ → Polynomial ℂ) (d : ℕ → ℕ)
    (B : ℕ → ℝ) (a : ℕ → ℕ → ℂ),
    c0184AdmissibleProfile k P d B a →
      Tendsto (fun L : ℕ => (d L : ℝ) / (L : ℝ)) atTop (𝓝 0) ∧
      Tendsto
        (fun L : ℕ =>
          B L / Real.rpow (L : ℝ) ((1 : ℝ) / (k : ℝ)))
        atTop (𝓝 0)

noncomputable def dWinterFactor (L : ℝ) (z : ℂ) : ℂ :=
  (z * Complex.sin ((L : ℂ) * z) - (1 / 2 : ℂ) * Complex.cos ((L : ℂ) * z)) /
    (z ^ 2 + (1 / 2 : ℂ) ^ 2)

noncomputable def claim15013 : Prop :=
  ∀ (L : ℝ) (z : ℂ),
    z ≠ Complex.I / 2 → z ≠ -Complex.I / 2 →
      dWinterFactor L z =
        (Complex.I / 2) * Complex.exp (-Complex.I * (L : ℂ) * z) /
            (z - Complex.I / 2) -
          (Complex.I / 2) * Complex.exp (Complex.I * (L : ℂ) * z) /
            (z + Complex.I / 2)

noncomputable def transitionScale (k L : ℕ) : ℝ :=
  Real.rpow (L : ℝ) ((1 : ℝ) / (2 * (k : ℝ)))

noncomputable def claim15016 : Prop :=
  ∀ (k : ℕ) (P : ℕ → Polynomial ℂ) (d : ℕ → ℕ)
    (B : ℕ → ℝ) (a : ℕ → ℕ → ℂ),
    c0184AdmissibleProfile k P d B a →
      ∀ y : ℝ, 0 < y →
        (∀ L : ℕ,
          ∃ Q : Polynomial ℂ,
            Q.natDegree ≤ 2 * d L ∧
              ∀ x : ℝ,
                Q.eval (x : ℂ) =
                  (P L).eval
                    (((x : ℂ) + Complex.I * (y : ℂ)) ^ 2 /
                      (transitionScale k L : ℂ) ^ 2)) ∧
        Tendsto
          (fun L : ℕ =>
            (P L).eval
              ((Complex.I * (y : ℂ)) ^ 2 /
                (transitionScale k L : ℂ) ^ 2))
          atTop (𝓝 1)

noncomputable def positiveMellin (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), Real.rpow x (s - 1) * f x

noncomputable def gaussian (x : ℝ) : ℝ :=
  Real.exp (-Real.pi * x ^ 2)

noncomputable def r0 (x : ℝ) : ℝ :=
  (1 - 2 * Real.pi * x ^ 2) * gaussian x

noncomputable def h (x : ℝ) : ℝ :=
  x ^ 2 * (2 * Real.pi * x ^ 2 - 3) * gaussian x

noncomputable def claim15036 : Prop :=
  ∀ s : ℝ, 0 < s →
    positiveMellin (fun x => x ^ 2 * gaussian x) s /
        positiveMellin gaussian s = s / (2 * Real.pi) ∧
      positiveMellin (fun x => x ^ 4 * gaussian x) s /
          positiveMellin gaussian s = s * (s + 2) / (4 * Real.pi ^ 2)

noncomputable def claim15037 : Prop :=
  ∀ s : ℝ, 0 < s →
    positiveMellin h s = s * (s - 1) / (2 * Real.pi) * positiveMellin gaussian s ∧
      positiveMellin r0 s = (1 - s) * positiveMellin gaussian s
>>>>>>> theirs

end MathlibPlus.Open.ResearchFormalizationBatch
