import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.ShellEdgeBatch

private noncomputable def shellEdge (N n m : ℕ) (u v : ℕ → ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    ∑ a ∈ Finset.range (min i.val j.val + 1),
      ((i.val + j.val + 1 - 2 * a : ℕ) : ℝ) * u a * v (i.val + j.val + 1 - a)

private noncomputable def completedBezout (N : ℕ) (h : ℕ → ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    ∑ a ∈ Finset.range (min i.val j.val + 1),
      ((i.val + j.val + 1 - 2 * a : ℕ) : ℝ) * h a * h (i.val + j.val + 1 - a)

private noncomputable def amplitudePolynomial (N : ℕ) (h s : ℕ → ℝ) : Polynomial ℝ :=
  Matrix.det (fun (i j : Fin N) =>
    ∑ a ∈ Finset.range (min i.val j.val + 1),
      Polynomial.C ((i.val + j.val + 1 - 2 * a : ℕ) : ℝ) *
        (Polynomial.C (h a) + Polynomial.X * Polynomial.C (s a)) *
        (Polynomial.C (h (i.val + j.val + 1 - a)) +
          Polynomial.X * Polynomial.C (s (i.val + j.val + 1 - a))))

/-- Claim 17522: the finite shell-pair edge formula with zero extension. -/
def claim17522 : Prop :=
  ∀ (N n m : ℕ) (u v : ℕ → ℝ),
    (∀ k, n < k → u k = 0) →
    (∀ k, m < k → v k = 0) →
    ∀ i j : Fin N,
      shellEdge N n m u v i j =
        ∑ a ∈ Finset.range (min i.val j.val + 1),
          ((i.val + j.val + 1 - 2 * a : ℕ) : ℝ) * u a * v (i.val + j.val + 1 - a)

/-- Claim 17523: the completed matrix is the sum of all shell-pair edges. -/
def claim17523 : Prop :=
  ∀ (M N : ℕ) (h : ∀ n : Fin (M + 1), ℕ → ℝ),
    (∀ (n : Fin (M + 1)) k, n.val < k → h n k = 0) →
    completedBezout N (fun k => ∑ n : Fin (M + 1), h n k) =
      ∑ n : Fin (M + 1), ∑ m : Fin (M + 1), shellEdge N n.val m.val (h n) (h m)

/-- Claim 17524: adding one shell gives the exact quadratic amplitude update. -/
def claim17524 : Prop :=
  ∀ (L N : ℕ) (h s : ℕ → ℝ) (w : ℝ),
    completedBezout N (fun k => h k + w * s k) =
      completedBezout N h +
        w • (shellEdge N L L h s + shellEdge N L L s h) +
        (w ^ 2) • completedBezout N s

/-- Claim 17526: the displayed rank-two update has the stated determinants. -/
def claim17526 : Prop :=
  let h : ℕ → ℝ := fun k =>
    match k with
    | 0 => 1
    | 1 => 7
    | 2 => 1
    | 3 => 2
    | _ => 0
  let s : ℕ → ℝ := fun k =>
    match k with
    | 0 => 11
    | 1 => 1
    | 2 => 19
    | 3 => 9
    | _ => 0
  let c₀ := completedBezout 2 h
  let c₁ := completedBezout 2 (fun k => h k + s k)
  c₀ 0 0 = 7 ∧ c₀ 0 1 = 2 ∧ c₀ 1 0 = 2 ∧ c₀ 1 1 = 13 ∧
    Matrix.det c₀ = 87 ∧ 0 < Matrix.det c₀ ∧
    c₁ 0 0 = 96 ∧ c₁ 0 1 = 480 ∧ c₁ 1 0 = 480 ∧ c₁ 1 1 = 556 ∧
    Matrix.det c₁ = -177024 ∧ Matrix.det c₁ < 0

/-- Claim 17527: shell repair is neither termwise positive nor monotone. -/
def claim17527 : Prop :=
  (∃ (N n m : ℕ) (u v : ℕ → ℝ) (i j : Fin N),
      (∀ k, n < k → u k = 0) ∧
      (∀ k, m < k → v k = 0) ∧
      shellEdge N n m u v i j < 0) ∧
  (∃ (h s : ℕ → ℝ), ¬ (∀ k : ℕ, 0 ≤ (amplitudePolynomial 4 h s).coeff k)) ∧
  (∃ (N : ℕ) (h s : ℕ → ℝ),
      0 < Matrix.det (completedBezout N h) ∧
      Matrix.det (completedBezout N (fun k => h k + s k)) <
        Matrix.det (completedBezout N h))

end MathlibPlus.Open.Analysis.ShellEdgeBatch
