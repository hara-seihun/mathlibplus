import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Exact real-valued proposition for the logarithmic endpoint-flat compactification. -/
def logarithmicEndpointFlatCompactification : Prop :=
  ∀ lam : ℝ, lam > 1 →
    let r : ℕ := ⌊Real.log lam⌋₊
    let m : ℕ := 2 * r + 2
    let w : ℝ → ℝ := fun x =>
      if |x| ≤ lam then (1 - x ^ 2 / lam ^ 2) ^ m else 0
    let h : ℝ → ℝ := fun x =>
      x ^ 2 * (2 * Real.pi * x ^ 2 - 3) * Real.exp (-Real.pi * x ^ 2)
    let g₀ : ℝ → ℝ := fun x => Real.exp (-Real.pi * x ^ 2)
    let b : ℝ :=
      (∫ x in (-lam)..lam, w x * h x) /
        (∫ x in (-lam)..lam, w x * g₀ x)
    let q : ℝ → ℝ := fun x =>
      if |x| ≤ lam then w x * (h x - b * g₀ x) else 0
    (∀ x : ℝ, q (-x) = q x) ∧
      (∫ x : ℝ, q x = 0) ∧
      (Function.support q ⊆ Set.Icc (-lam) lam) ∧
      (∀ k : ℕ, k < m →
        iteratedDeriv k q (-lam) = 0 ∧ iteratedDeriv k q lam = 0)

/-- Exact coefficient asymptotic and eventual center positivity. -/
def correctionCoefficientAndCenterAsymptotics : Prop :=
  let mN : ℝ → ℕ := fun lam => 2 * ⌊Real.log lam⌋₊ + 2
  let m : ℝ → ℝ := fun lam => (mN lam : ℝ)
  let w : ℝ → ℝ → ℝ := fun lam x =>
    if |x| ≤ lam then (1 - x ^ 2 / lam ^ 2) ^ (mN lam) else 0
  let h : ℝ → ℝ := fun x =>
    x ^ 2 * (2 * Real.pi * x ^ 2 - 3) * Real.exp (-Real.pi * x ^ 2)
  let g₀ : ℝ → ℝ := fun x => Real.exp (-Real.pi * x ^ 2)
  let b : ℝ → ℝ := fun lam =>
    if lam > 1 then
      (∫ x in (-lam)..lam, w lam x * h x) /
        (∫ x in (-lam)..lam, w lam x * g₀ x)
    else 0
  let q : ℝ → ℝ → ℝ := fun lam x =>
    if lam > 1 ∧ |x| ≤ lam then w lam x * (h x - b lam * g₀ x) else 0
  ∃ C : ℝ, 0 ≤ C ∧
    (∀ᶠ lam : ℝ in Filter.atTop,
      let base := -(3 * m lam) / (2 * Real.pi ^ 2 * lam ^ 2)
      |b lam - base| ≤ C * |base| * (m lam / lam ^ 2)) ∧
    (∀ᶠ lam : ℝ in Filter.atTop, q lam 0 = -b lam ∧ 0 < q lam 0)

/-- Exact compact-source L¹ bounds on the positive half-interval. -/
def compactSourceL1Approximation : Prop :=
  let mN : ℝ → ℕ := fun lam => 2 * ⌊Real.log lam⌋₊ + 2
  let m : ℝ → ℝ := fun lam => (mN lam : ℝ)
  let w : ℝ → ℝ → ℝ := fun lam x =>
    if |x| ≤ lam then (1 - x ^ 2 / lam ^ 2) ^ (mN lam) else 0
  let h : ℝ → ℝ := fun x =>
    x ^ 2 * (2 * Real.pi * x ^ 2 - 3) * Real.exp (-Real.pi * x ^ 2)
  let g₀ : ℝ → ℝ := fun x => Real.exp (-Real.pi * x ^ 2)
  let b : ℝ → ℝ := fun lam =>
    if lam > 1 then
      (∫ x in (-lam)..lam, w lam x * h x) /
        (∫ x in (-lam)..lam, w lam x * g₀ x)
    else 0
  let q : ℝ → ℝ → ℝ := fun lam x =>
    if lam > 1 ∧ |x| ≤ lam then w lam x * (h x - b lam * g₀ x) else 0
  ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
    (∀ᶠ lam : ℝ in Filter.atTop,
      (∫ x in (0)..lam, |q lam x - h x|) ≤ C₁ * (m lam / lam ^ 2) ∧
      (∫ x in (0)..lam, |q lam x - h x|) ≤
        C₂ * (Real.log lam / lam ^ 2))

/-- Exact growing-order Gaussian--Euler domination assertion. -/
def growingOrderGaussianEulerBound : Prop :=
  let mN : ℝ → ℕ := fun lam => 2 * ⌊Real.log lam⌋₊ + 2
  let w : ℝ → ℝ → ℝ := fun lam x =>
    if |x| ≤ lam then (1 - x ^ 2 / lam ^ 2) ^ (mN lam) else 0
  let h : ℝ → ℝ := fun x =>
    x ^ 2 * (2 * Real.pi * x ^ 2 - 3) * Real.exp (-Real.pi * x ^ 2)
  let g₀ : ℝ → ℝ := fun x => Real.exp (-Real.pi * x ^ 2)
  let b : ℝ → ℝ := fun lam =>
    if lam > 1 then
      (∫ x in (-lam)..lam, w lam x * h x) /
        (∫ x in (-lam)..lam, w lam x * g₀ x)
    else 0
  let q : ℝ → ℝ → ℝ := fun lam x =>
    if lam > 1 ∧ |x| ≤ lam then w lam x * (h x - b lam * g₀ x) else 0
  let D : (ℝ → ℝ) → ℝ → ℝ := fun f x => x * deriv f x
  let L : (ℝ → ℝ) → ℝ → ℝ :=
    fun f x => -(D (D f) x + D f x)
  let g : ℕ → ℝ → ℝ → ℝ := fun j lam => (L^[j]) (q lam)
  let l1 : (ℝ → ℝ) → ℝ := fun f => ∫ x : ℝ, ‖f x‖
  let r : ℝ → ℕ := fun lam => ⌊Real.log lam⌋₊
  ∃ C : ℝ, 0 < C ∧ ∃ C₀ : ℕ, ∃ M : ℕ → ℝ,
    (∀ n : ℕ, 0 ≤ M n ∧ M n ≤ (C * (n : ℝ)) ^ (2 * n + C₀)) ∧
    (∀ lam : ℝ, lam > 1 →
      l1 (g (r lam) lam) +
          l1 (deriv (deriv (g (r lam) lam))) ≤ M (r lam) ∧
      (∀ j : ℕ, j < r lam →
        let s := 2 * (r lam - j) + 2
        l1 (iteratedDeriv s (g j lam)) +
            l1 (iteratedDeriv s (fun x => x * g j lam x)) ≤ M (r lam)))

/-- Exact center-orthogonality assertion for the polynomial--Gaussian modes. -/
def centerOrthogonalPolynomialGaussianModes : Prop :=
  ∀ j : ℕ, 1 ≤ j →
    ∃ aⱼ : ℝ,
      ∫ x : ℝ,
        (x ^ (4 * j) - aⱼ * x ^ 2) *
          (x ^ 2 * (2 * Real.pi * x ^ 2 - 3) *
            Real.exp (-Real.pi * x ^ 2)) = 0

end MathlibPlus.Open.Analysis
