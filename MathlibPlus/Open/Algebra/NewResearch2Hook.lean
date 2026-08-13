import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Algebra.NewResearch2

noncomputable section

/-- Claim 1785: the exact hook array, principal product, and row set. -/
def flaggedHookDataPrincipalProduct_claim1785 : Prop :=
  ∀ (d : ℕ) (a : ℝ),
    let A : ℝ → ℕ → ℕ → ℝ := fun x r j =>
      (r + 1 : ℝ) * if r + 1 ≤ 2 * j then
        ∑ f : Fin (r + 2) → Fin (2 * j + 1),
          if (∑ i, (f i).val) = 2 * j - r - 1 then
            ∏ i, (x + (i.1 : ℝ)) ^ (f i).val else 0
      else 0
    (∀ r j, r < 2 * d → 1 ≤ j → j ≤ d → A a r j = A a r j) ∧
      Matrix.det (fun (i : Fin d) (j : Fin d) => A a i.1 (j.1 + 1)) =
        (Nat.factorial d : ℝ) *
          Finset.prod (Finset.range (d + 1)) (fun p =>
            Finset.prod (Finset.range (d + 1)) (fun q =>
              if p < q then 2 * (a - 1 / 2) + (p + q + 1 : ℕ) else 1)) ∧
      ∀ (n ell : ℕ), 1 ≤ n → n ≤ d → ell < d →
        let e := d - ell
        ∀ i : Fin d,
          (if i.1 < e - 1 then i.1
            else if i.1 < d - 1 then i.1 + 1 else d + n - 1) =
          (if i.1 < e - 1 then i.1
            else if i.1 < d - 1 then i.1 + 1 else d + n - 1)

/-- Claim 1786: exact hook Newton-tail matrix and ratio. -/
def exactHookNewtonTailRatio_claim1786 : Prop :=
  ∀ (a : ℝ) (d n ell : ℕ), 1 ≤ n → n ≤ d → ell < d →
    let e := d - ell
    let Y := 2 * a + d
    let t : Fin (ell + 1) → ℕ := fun i => if i.1 < ell then i.1 + 1 else ell + n
    let tail : Fin (ell + 1) → Fin (ell + 1) → ℝ := fun i j =>
      (Nat.choose (e + j.1) (t i - j.1) : ℝ) /
        Finset.prod (Finset.range (t i - j.1)) (fun r => Y - ell + j.1 + r)
    let D : ℝ := Matrix.det tail
    let Z : ℝ := ((d + n : ℝ) / e) * D
    let denominator : ℝ :=
      Finset.prod (Finset.range (n + ell)) (fun r => Y - ell + r)
    let A : ℝ → ℕ → ℕ → ℝ := fun x r j =>
      (r + 1 : ℝ) * if r + 1 ≤ 2 * j then
        ∑ f : Fin (r + 2) → Fin (2 * j + 1),
          if (∑ i, (f i).val) = 2 * j - r - 1 then
            ∏ i, (x + (i.1 : ℝ)) ^ (f i).val else 0
      else 0
    let K : Fin d → ℕ := fun i =>
      if i.1 < e - 1 then i.1
      else if i.1 < d - 1 then i.1 + 1 else d + n - 1
    let Hhook : ℝ := Matrix.det
      (fun (i : Fin d) (j : Fin d) => A a (K i) (j.1 + 1))
    let Hempty : ℝ := Matrix.det
      (fun (i : Fin d) (j : Fin d) => A a i.1 (j.1 + 1))
    Hhook / Hempty = Z / denominator ∧
      (∀ i j, tail i j =
        (Nat.choose (e + j.1) (t i - j.1) : ℝ) /
          Finset.prod (Finset.range (t i - j.1))
            (fun r => Y - ell + j.1 + r))

/-- Claim 1787: inverse Riordan cofactor formula. -/
def inverseRiordanCofactorFormula_claim1787 : Prop :=
  ∀ (e ell n : ℕ),
    let R : ℕ → ℕ → ℚ := fun t j =>
      if j ≤ t then (Nat.choose (e + j) (t - j) : ℚ) else 0
    let q : ℕ → ℚ := fun j =>
      if j = 0 then 1 else
        (-1 : ℚ) ^ j * (e : ℚ) / (j : ℚ) *
          (Nat.choose (e + 2 * j - 1) (j - 1) : ℚ)
    let D : ℚ := Matrix.det
      (fun (i : Fin (ell + 1)) (j : Fin (ell + 1)) =>
        R (if i.1 < ell then i.1 + 1 else ell + n) j.1)
    (∀ t0 : ℕ, ∑ j ∈ Finset.range (t0 + 1), R t0 j * q j =
      if t0 = 0 then 1 else 0) ∧
      D = (-1 : ℚ) ^ ell *
        ∑ j ∈ Finset.range (ell + 1), q j *
          (Nat.choose (e + j) (n + ell - j) : ℚ)

/-- Claim 1790: first-row gap minor identity and nonnegativity. -/
def firstRowGapMinorIdentity_claim1790 : Prop :=
  ∀ (e ell n : ℕ), 1 ≤ ell →
    let R : ℕ → ℕ → ℤ := fun t j =>
      if j ≤ t then (Nat.choose (e + j) (t - j) : ℤ) else 0
    let D : ℕ → ℕ → ℕ → ℤ := fun ee ll nn =>
      Matrix.det (fun (i : Fin (ll + 1)) (j : Fin (ll + 1)) =>
        R (if i.1 < ll then i.1 + 1 else ll + nn) j.1)
    let A : ℕ → ℕ → ℕ → ℤ := fun ee ll nn =>
      Matrix.det (fun (i : Fin ll) (j : Fin ll) =>
        R (if i.1 < ll - 1 then i.1 + 2 else ll + nn)
          (if j.1 = 0 then 0 else j.1 + 1))
    D e ell n = (e : ℤ) * D (e + 1) (ell - 1) n - A e ell n ∧ 0 ≤ A e ell n

/-- Claim 1791: last-rise endpoint inequalities. -/
def lastRiseEndpointInequalities_claim1791 : Prop :=
  ∀ (e ell n : ℕ), 1 ≤ ell → 2 ≤ n →
    let R : ℕ → ℕ → ℤ := fun t j =>
      if j ≤ t then (Nat.choose (e + j) (t - j) : ℤ) else 0
    let D : ℕ → ℕ → ℕ → ℤ := fun ee ll nn =>
      Matrix.det (fun (i : Fin (ll + 1)) (j : Fin (ll + 1)) =>
        R (if i.1 < ll then i.1 + 1 else ll + nn) j.1)
    let A : ℕ → ℕ → ℕ → ℤ := fun ee ll nn =>
      Matrix.det (fun (i : Fin ll) (j : Fin ll) =>
        R (if i.1 < ll - 1 then i.1 + 2 else ll + nn)
          (if j.1 = 0 then 0 else j.1 + 1))
    D e ell n ≤ (e + ell : ℤ) * D e ell (n - 1) ∧
      A e ell n ≤ (e + ell : ℤ) * A e ell (n - 1)

/-- Claim 1797: hook denominator cancellation and endpoint witnesses. -/
def hookDenominatorCancellation_claim1797 : Prop :=
  ∀ (d n ell : ℕ), 1 ≤ n → n ≤ d → ell < d →
    let Xp : Polynomial ℚ := Polynomial.X
    let factor : ℕ → ℕ → Polynomial ℚ := fun p q =>
      2 * Xp + Polynomial.C (p + q + 1 : ℚ)
    let P : Polynomial ℚ := (Nat.factorial d : Polynomial ℚ) *
      Finset.prod (Finset.range (d + 1)) (fun p =>
        Finset.prod (Finset.range (d + 1)) (fun q =>
          if p < q then factor p q else 1))
    let Delta : Polynomial ℚ := Finset.prod (Finset.range (n + ell))
      (fun r => 2 * Xp + Polynomial.C (d + 1 - ell + r : ℚ))
    Delta ∣ P ∧
      (∀ r, r < ell → factor 0 (d - ell + r) =
        2 * Xp + Polynomial.C (d + 1 - ell + r : ℚ)) ∧
      (∀ s, s < n → factor s d =
        2 * Xp + Polynomial.C (d + 1 + s : ℚ))

end

end MathlibPlus.Open.Algebra.NewResearch2
