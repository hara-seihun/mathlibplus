import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization

/-- General one-log-scale resonance theorem with the weighted prime mass, the
critical Mellin energy, and the exact concentration hypotheses. -/
def claim11413 : Prop :=
  ∀ (c σ : ℝ)
    (q : ℕ → {p : ℕ // Nat.Prime p} → ℝ)
    (lambdaY : ℕ → ℝ),
    (1 < c ∧ c < 3 / 2 ∧ σ = 2 - c ∧ 1 / 2 < σ ∧ σ < 1) →
    (∃ M : ℝ, ∀ Y p, 0 ≤ q Y p ∧ q Y p ≤ M) →
    let L : ℕ → ℝ := fun Y =>
      ∑' p : {p : ℕ // Nat.Prime p},
        q Y p * Real.rpow (p.1 : ℝ) (-σ)
    let A : ℕ → ℂ → ℂ := fun Y z =>
      Complex.exp
        (∑' p : {p : ℕ // Nat.Prime p},
          (q Y p : ℂ) *
            Complex.log (1 - Complex.cpow (p.1 : ℂ) (-z)))
    let E : ℕ → ℝ := fun Y =>
      (2 * Real.pi)⁻¹ *
        ∫ t : ℝ,
          ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 *
            ‖A Y ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
    let V : ℕ → ℝ := fun Y =>
      ∑' p : {p : ℕ // Nat.Prime p},
        q Y p * Real.rpow (p.1 : ℝ) (-σ) *
          |Real.log (p.1 : ℝ) - lambdaY Y|
    Filter.Tendsto L Filter.atTop Filter.atTop →
    Filter.Tendsto lambdaY Filter.atTop Filter.atTop →
    Asymptotics.IsLittleO Filter.atTop V (fun Y => L Y * lambdaY Y) →
    Asymptotics.IsLittleO Filter.atTop
      (fun Y => Real.log (lambdaY Y * L Y)) L →
    Asymptotics.IsLittleO Filter.atTop
      (fun Y => Real.log (E Y) - 2 * L Y) L ∧
      Filter.Tendsto E Filter.atTop Filter.atTop

/-- The adverse phase and its uniform shrinking-interval lower bound. -/
def claim11414 : Prop :=
  ∀ (c σ : ℝ)
    (q : ℕ → {p : ℕ // Nat.Prime p} → ℝ)
    (lambdaY : ℕ → ℝ),
    (1 < c ∧ c < 3 / 2 ∧ σ = 2 - c ∧ 1 / 2 < σ ∧ σ < 1) →
    (∃ M : ℝ, ∀ Y p, 0 ≤ q Y p ∧ q Y p ≤ M) →
    let L : ℕ → ℝ := fun Y =>
      ∑' p : {p : ℕ // Nat.Prime p},
        q Y p * Real.rpow (p.1 : ℝ) (-σ)
    let P : ℕ → ℂ → ℂ := fun Y z =>
      ∑' p : {p : ℕ // Nat.Prime p},
        (q Y p : ℂ) * Complex.cpow (p.1 : ℂ) (-z)
    let V : ℕ → ℝ := fun Y =>
      ∑' p : {p : ℕ // Nat.Prime p},
        q Y p * Real.rpow (p.1 : ℝ) (-σ) *
          |Real.log (p.1 : ℝ) - lambdaY Y|
    let tY : ℕ → ℝ := fun Y => Real.pi / lambdaY Y
    let δY : ℕ → ℝ := fun Y =>
      1 / (lambdaY Y * Real.sqrt (L Y))
    Filter.Tendsto L Filter.atTop Filter.atTop →
    Filter.Tendsto lambdaY Filter.atTop Filter.atTop →
    Asymptotics.IsLittleO Filter.atTop V (fun Y => L Y * lambdaY Y) →
    Asymptotics.IsLittleO Filter.atTop
      (fun Y => Real.log (lambdaY Y * L Y)) L →
    Asymptotics.IsLittleO Filter.atTop
      (fun Y =>
        P Y ((σ : ℂ) + (tY Y : ℂ) * Complex.I) + (L Y : ℂ))
      (fun Y => (L Y : ℂ)) ∧
    (∃ r : ℕ → ℝ,
      Asymptotics.IsLittleO Filter.atTop r L ∧
        ∀ᶠ Y in Filter.atTop, ∀ t : ℝ,
          |t - tY Y| ≤ δY Y →
            L Y - r Y ≤
              -((P Y ((σ : ℂ) + (t : ℂ) * Complex.I)).re)) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ᶠ Y in Filter.atTop, ∀ t : ℝ,
        |t - tY Y| ≤ δY Y →
          C ≤ ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I)‖)

/-- Primorial Euler polynomial, Nyman approximant, and exact defect transform. -/
def claim11424 : Prop :=
  let primeSet : ℕ → Finset ℕ := fun y =>
    Finset.filter Nat.Prime (Finset.Icc 2 y)
  let Q : ℕ → ℕ := fun y =>
    ∏ p ∈ primeSet y, p
  let A : ℕ → ℂ → ℂ := fun y s =>
    ∑ d ∈ Nat.divisors (Q y),
      ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        Complex.cpow (d : ℂ) (-s)
  let Aprod : ℕ → ℂ → ℂ := fun y s =>
    ∏ p ∈ primeSet y, (1 - Complex.cpow (p : ℂ) (-s))
  let a : ℕ → ℝ := fun y =>
    ∑ d ∈ Nat.divisors (Q y),
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) / (d : ℝ)
  let aprod : ℕ → ℝ := fun y =>
    ∏ p ∈ primeSet y, (1 - (p : ℝ)⁻¹)
  let b : ℝ → ℝ → ℝ := fun α x =>
    Int.fract (α / x) - α * Int.fract (1 / x)
  let v : ℕ → ℝ → ℝ := fun y x =>
    -∑ d ∈ Nat.divisors (Q y),
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        b (1 / (d : ℝ)) x
  let g : ℕ → ℝ → ℝ := fun y x => 1 - v y x
  let ghat : ℕ → ℂ → ℂ := fun y s =>
    ∫ x in Set.Ioo (0 : ℝ) 1,
      ((g y x : ℝ) : ℂ) * Complex.cpow (x : ℂ) (s - 1)
  (∀ y s, A y s = Aprod y s) ∧
  (∀ y, a y = aprod y) ∧
  (∀ (y : ℕ) (s : ℂ), 0 < s.re → s.re < 1 →
    ghat y s =
      (1 - riemannZeta s * (A y s - (a y : ℂ))) / s)

/-- Grouping the periodic reduced-residue discrepancy by residues gives the
finite digamma expression for the squared L2 defect. -/
def claim11427 : Prop :=
  let primeSet : ℕ → Finset ℕ := fun y =>
    Finset.filter Nat.Prime (Finset.Icc 2 y)
  let Q : ℕ → ℕ := fun y =>
    ∏ p ∈ primeSet y, p
  let b : ℝ → ℝ → ℝ := fun α x =>
    Int.fract (α / x) - α * Int.fract (1 / x)
  let v : ℕ → ℝ → ℝ := fun y x =>
    -∑ d ∈ Nat.divisors (Q y),
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        b (1 / (d : ℝ)) x
  let g : ℕ → ℝ → ℝ := fun y x => 1 - v y x
  let C : ℕ → ℕ → ℕ := fun q n =>
    (Finset.filter (fun m => Nat.gcd m q = 1) (Finset.Icc 1 n)).card
  let D : ℕ → ℕ → ℝ := fun q n =>
    1 + (n : ℝ) * (Nat.totient q : ℝ) / (q : ℝ) - (C q n : ℝ)
  let normSq : ℕ → ℝ := fun y =>
    ∫ x in Set.Ioo (0 : ℝ) 1, (g y x) ^ 2
  (∀ y : ℕ, normSq y =
    (Q y : ℝ)⁻¹ *
      ∑ r ∈ Finset.Icc 1 (Q y),
        (D (Q y) r) ^ 2 *
          ((Complex.digamma
              (((r + 1 : ℕ) : ℝ) / (Q y : ℝ) : ℂ)).re -
            (Complex.digamma
              ((r : ℝ) / (Q y : ℝ) : ℂ)).re))

end MathlibPlus.Open.ResearchFormalization
